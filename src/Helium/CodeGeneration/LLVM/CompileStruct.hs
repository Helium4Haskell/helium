module Helium.CodeGeneration.LLVM.CompileStruct where

import Data.Bits (shiftL)
import Data.Maybe (isJust)
import Data.List (zipWith4)
import Lvm.Common.Id(idFromString, Id, NameSupply, mapWithSupply, splitNameSupply, splitNameSupplies)
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Struct
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins
import LLVM.AST as AST hiding (Struct)
import LLVM.AST.CallingConvention
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import qualified LLVM.AST.Constant as Constant
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate

idHeaderPtr = idFromString "$headerPtr"
idHeaderValue = idFromString "$headerValue"
idFieldPtr = idFromString "$fieldPtr"

-- Ceil of a/b
divCeiling :: Int -> Int -> Int
divCeiling a b = (a + b - 1) `div` b

structType :: Env -> Struct -> Type
structType _ (Struct (Just name) _ _ _) = NamedTypeReference name
structType env struct = structTypeNoAlias env struct

structTypeNoAlias :: Env -> Struct -> Type
structTypeNoAlias env struct = StructureType False (headerStruct : fieldTypes)
  where
    -- Search the last flag to find the number of additional header fields (after the field containing the garbage collector bits)
    (additionalHeaderFields, _) = findFlagInHeader env struct (flagCount struct - 1)
    headerStruct = StructureType False $ IntegerType (fromIntegral $ firstFieldSize $ envTarget env) : replicate additionalHeaderFields (envValueType env)
    getFieldType :: StructField -> Type
    getFieldType (StructField Iridium.TypeAny _) = voidPointer
    getFieldType (StructField t _) = compileType env t
    fieldTypes = map getFieldType $ fields struct
-- Example for a 32 bit system, with 48 gc bits. The first header element thus needs 64 bits (first multiple of 32 bits larger than 48).
-- If the tag is large or if there are many flags needed, we need additional 32-bit sized fields.
-- { { i64, i32, i32 }, i8*, i8*, i8*, i8* }

flagCount :: Struct -> Int
flagCount struct = length (filter (\f -> isJust $ fieldFlagIndex f) $ fields struct)

sizeOf :: Target -> Struct -> Int
sizeOf target struct = words * wordSize `div` 8
  where
    headerBits = targetGarbageCollectorBits target + tagSize struct + flagCount struct
    headerWords = headerBits `divCeiling` wordSize
    wordSize = targetWordSize target
    words = headerWords + length (fields struct)

findFlagInHeader :: Env -> Struct -> Int -> (Int, Int)
findFlagInHeader env struct index
  | index < flagsInFirstWord = (0, index)
  | otherwise = (indexAfterFirstElement `div` wordSize, indexAfterFirstElement `mod` wordSize)
  where
    target = envTarget env
    firstField = firstFieldSize target
    wordSize = targetWordSize target
    tagInFirst = tagInFirstElement env struct
    flagsInFirstWord = firstFieldSize target - targetGarbageCollectorBits target - (if tagInFirst then tagSize struct else 0)
    -- The index, projected to the second element. Eg the first bit of the second element has projected index 0.
    indexAfterFirstElement = index - flagsInFirstWord + (if tagInFirst then 0 else tagSize struct)

-- We store the garbage collector data in the first field. We thus might need to
-- multiple words to store this
firstFieldSize :: Target -> Int
firstFieldSize target = wordCount * targetWordSize target
  where wordCount = targetGarbageCollectorBits target `divCeiling` targetWordSize target

tagInFirstElement :: Env -> Struct -> Bool
tagInFirstElement env struct = tagSize struct + targetGarbageCollectorBits target <= firstFieldSize (envTarget env)
  where
    target = envTarget env

allocate :: Env -> Name -> Name -> Type -> Struct -> [Named Instruction]
allocate env nameVoid name t struct =
  [ nameVoid := Call Nothing Fast [] (Right Builtins.alloc) [(ConstantOperand $ Constant.Int 32 3, []), (ConstantOperand $ Constant.Int 32 $ fromIntegral $ sizeOf (envTarget env) struct, [])] [] []
  , name := BitCast (LocalReference voidPointer nameVoid) (pointer t) []
  ]

headerElementSize :: Env -> Int -> Int
headerElementSize env 0 = firstFieldSize $ envTarget env
headerElementSize env _ = targetWordSize $ envTarget env

initialize :: NameSupply -> Env -> Operand -> Struct -> [(Operand, Operand)] -> [Named Instruction]
initialize supply env reference struct fieldValues = writeInstructions ++ headerInstructions
  where
    -- Search the last flag to find the number of additional header fields (after the field containing the garbage collector bits)
    (additionalHeaderFields, _) = findFlagInHeader env struct (flagCount struct - 1)

    (supplyHeader, supplyFields) = splitNameSupply supply

    initialHeader = ConstantOperand (Constant.Int (fromIntegral $ headerElementSize env 0) (initialHeaderValue 0))
      : map (\i -> ConstantOperand $ Constant.Int (fromIntegral $ headerElementSize env i) (initialHeaderValue i)) [0..additionalHeaderFields - 1]
    initialHeaderValue index
      | index == 0 && tagInFirstElement env struct = fromIntegral $ tagValue struct `shiftL` targetGarbageCollectorBits (envTarget env)
      | index == 1 && not (tagInFirstElement env struct) = fromIntegral $ tagValue struct
      | otherwise = 0

    (finalHeader, writeInstructions) = writeFields supplyHeader env reference struct (map Just fieldValues) initialHeader

    headerInstructions = writeHeaderFields supplyHeader env reference (map Just finalHeader)

writeHeaderFields :: NameSupply -> Env -> Operand -> [Maybe Operand] -> [Named Instruction]
writeHeaderFields supply env reference fields = concat $ mapWithSupply writeHeaderField supply $ zip fields [0..]
  where
    writeHeaderField :: NameSupply -> (Maybe Operand, Int) -> [Named Instruction]
    writeHeaderField _ (Nothing, _) = []
    writeHeaderField s (Just valueOperand, i) =
      [ namePtr := getElementPtr reference [0, 0, i]
      , Do $ Store False (LocalReference (pointer $ IntegerType $ fromIntegral $ headerElementSize env i) namePtr) valueOperand Nothing 0 []
      ]
      where
        (namePtr, _) = freshNameFromId idHeaderPtr s

-- TODO: For updates, also use a bit mask to reset the flags in the header, of the fields 
writeFields :: NameSupply -> Env -> Operand -> Struct -> [Maybe (Operand, Operand)] -> [Operand] -> ([Operand], [Named Instruction])
writeFields supply env operand struct values headers = foldr f (headers, []) compiledFields
  where
    f :: ([Operand] -> ([Operand], [Named Instruction])) -> ([Operand], [Named Instruction]) -> ([Operand], [Named Instruction])
    f field (headers, instrs) = (newHeaders, fInstrs ++ instrs)
      where
        (newHeaders, fInstrs) = field headers
    compiledFields :: [[Operand] -> ([Operand], [Named Instruction])]
    compiledFields = zipWith4 (writeField env operand struct) (splitNameSupplies supply) [0..] (fields struct) values

writeField :: Env -> Operand -> Struct -> NameSupply -> Int -> StructField -> Maybe (Operand, Operand) -> [Operand] -> ([Operand], [Named Instruction])
writeField _ _ _ _ _ _ Nothing _ = ([], [])
writeField env operand struct supply fieldIdx (StructField fType fFlagIndex) (Just (opValue, opIsWhnf)) headers = (newHeaders, updateHeader ++ fieldInstructions)
  where
    (supplyField, supplyHeader) = splitNameSupply supply

    -- Field
    (nameElementPtr, _) = freshNameFromId idFieldPtr supplyField
    fieldCompiledType = case fType of
      Iridium.TypeAny -> voidPointer -- The flag is stored in the header instead of in the field
      _ -> compileType env fType
    fieldInstructions :: [Named Instruction]
    fieldInstructions =
      [ nameElementPtr := getElementPtr operand [0, fieldIdx + 1]
      , Do $ Store False (LocalReference (pointer fieldCompiledType) nameElementPtr) opValue Nothing 0 []
      ]

    -- Headers
    updateHeader :: [Named Instruction]
    newHeaders :: [Operand]
    (updateHeader, newHeaders) = case fFlagIndex of
      Nothing -> ([], headers)
      Just index ->
        let
          (headerIdx, bitIdx) = findFlagInHeader env struct index
          (nameExtended, supplyHeader') = freshName supplyHeader
          (nameShifted, supplyHeader'') = freshName supplyHeader'
          (nameHeader, _) = freshNameFromId idHeaderValue supplyHeader''
          headerBits = headerElementSize env headerIdx
          headerType = IntegerType $ fromIntegral headerBits
        in
          ( [ nameExtended := ZExt opIsWhnf headerType []
            , nameShifted := Shl False False (LocalReference headerType nameExtended) (ConstantOperand $ Constant.Int (fromIntegral headerBits) (fromIntegral bitIdx)) []
            , nameHeader := Xor (headers !! headerIdx) (LocalReference headerType nameShifted) []
            ]
          , take (headerIdx - 1) headers ++ [LocalReference headerType nameHeader] ++ drop headerIdx headers
          )

checkTag :: NameSupply -> Env -> Operand -> Struct -> Name -> [Named Instruction]
checkTag supply env reference struct name
  | tagSize struct == 0 = [ name := BitCast (ConstantOperand $ Constant.Int 1 0) (IntegerType 1) [] ]
  | otherwise =
    [ headerPtr := getElementPtr reference [0, 0, headerIdx]
    , headerValue := Load False (LocalReference (pointer headerType) headerPtr) Nothing 0 []
    , headerShifted := LShr False (LocalReference headerType headerValue) (ConstantOperand $ Constant.Int (fromIntegral headerBits) $ fromIntegral shift) []
    , headerTrunc := Trunc (LocalReference headerType headerShifted) tagType []
    -- , name := ZExt (LocalReference (IntegerType $ fromIntegral $ tagSize struct) headerTrunc) (envValueType env) []
    , name := ICmp IntegerPredicate.EQ (LocalReference tagType headerTrunc) (ConstantOperand $ Constant.Int (fromIntegral $ tagSize struct) $ fromIntegral $ tagValue struct) []
    ]
  where
    (headerIdx, shift)
      | tagInFirstElement env struct = (0, targetGarbageCollectorBits $ envTarget $ env)
      | otherwise = (1, 0)
    headerBits = headerElementSize env headerIdx
    headerType = IntegerType $ fromIntegral headerBits
    tagType = IntegerType $ fromIntegral $ tagSize struct
    (headerPtr, supply1) = freshNameFromId idHeaderPtr supply
    (headerValue, supply2) = freshNameFromId idHeaderValue supply1
    (headerShifted, supply3) = freshName supply2
    (headerTrunc, _) = freshName supply3

extractField :: NameSupply -> Env -> Operand -> Struct -> Int -> StructField -> Name -> [Named Instruction]
extractField supply env reference _ index (StructField t Nothing) name =
  [ namePtr := getElementPtr reference [0, index]
  , name := Load False (LocalReference (compileType env t) namePtr) Nothing 0 []
  ]
  where
    (namePtr, _) = freshNameFromId idFieldPtr supply
extractField supply env reference struct index (StructField t (Just flagIndex)) name =
  [ namePtr := getElementPtr reference [0, index]
  , nameValue := Load False (LocalReference voidPointer namePtr) Nothing 0 []
  , headerPtr := getElementPtr reference [0, 0, headerIdx]
  , headerValue := Load False (LocalReference (pointer $ headerType) headerPtr) Nothing 0 []
  , headerShifted := LShr False (LocalReference headerType headerValue) (ConstantOperand $ Constant.Int (fromIntegral headerBits) $ fromIntegral bitIdx) []
  , isWhnf := Trunc (LocalReference headerType headerShifted) bool []
  , nameStruct := InsertValue (ConstantOperand emptyStruct) (LocalReference voidPointer nameValue) [0] []
  , name := InsertValue (LocalReference taggedThunkPointer nameStruct) (LocalReference bool isWhnf) [1] []
  ]
  where
    (headerIdx, bitIdx) = findFlagInHeader env struct flagIndex
    headerBits = headerElementSize env headerIdx
    headerType = IntegerType $ fromIntegral headerBits
    emptyStruct :: Constant.Constant
    emptyStruct = Constant.Struct Nothing True [Constant.Undef voidPointer, Constant.Undef bool]
    -- Names
    (namePtr, supply1) = freshNameFromId idFieldPtr supply
    (nameValue, supply2) = freshName supply1
    (headerPtr, supply3) = freshNameFromId idHeaderPtr supply2
    (headerValue, supply4) = freshNameFromId idHeaderValue supply3
    (headerShifted, supply5) = freshName supply4
    (isWhnf, supply6) = freshName supply5
    (nameStruct, _) = freshName supply6
