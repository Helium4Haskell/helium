module Helium.CodeGeneration.LLVM.CompileConstructor (constructorType, compileAllocation, compileExtractFields) where

import qualified Data.Bits as Bits
import Data.Word(Word32)

import Lvm.Common.Id(Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv
import LLVM.AST as AST
import LLVM.AST.CallingConvention
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import LLVM.AST.Constant as Constant

constructorType :: Env -> ConstructorLayout -> Type
constructorType env (LayoutInline tag) = envValueType env
constructorType env (LayoutPointer _ _ headerSize fieldLayouts) = StructureType True $ headerType : fieldTypes
  where
    headerType = IntegerType $ fromIntegral $ pointerSize * headerSize
    pointerSize = targetPointerSize $ envTarget env
    -- TODO: This code assumes that the fields are not reordered. If we add strictness annotations on fields
    -- and reorder fields, this code must be changed.
    fieldTypes = map mapFieldType fieldLayouts
    mapFieldType :: ConstructorFieldLayout -> Type
    mapFieldType (ConstructorFieldLayout Iridium.TypeAny _ _) = voidPointer
    mapFieldType (ConstructorFieldLayout t _ _) = compileType env t
 
compileAllocation :: Env -> NameSupply -> Id -> [Id] -> Name -> [Named Instruction]
compileAllocation env supply conId args varName = concat splitInstructions ++ compileAllocation' env supplyAlloc conId con argsSplit varName
  where
    con = findMap conId (envConstructors env)
    (supplyArgs, supplyAlloc) = splitNameSupply supply
    splitInstructions :: [[Named Instruction]]
    argsSplit :: [(Operand, Operand)]
    (splitInstructions, argsSplit) = unzip $ mapWithSupply (splitValueFlag env) supplyArgs args

compileAllocation' :: Env -> NameSupply -> Id -> ConstructorLayout -> [(Operand, Operand)] -> Name -> [Named Instruction]
compileAllocation' env _ _ (LayoutInline tag) _ varName = [varName := AST.IntToPtr (ConstantOperand $ Int (fromIntegral $ targetPointerSize $ envTarget env) value) voidPointer []]
  where
    -- Put a '1' in the least significant bit to distinguish it from a pointer.
    value :: Integer
    value = fromIntegral tag * 2 + 1

-- TODO: Set proper alignment as the first argument of `alloc`.
compileAllocation' env supply conId layout@(LayoutPointer tag (firstTagBit, _) headerSize fieldLayouts) args varName =
  [ varName := Call Nothing Fast [] (Right Builtins.alloc) [(ConstantOperand $ Int 32 8, []), (ConstantOperand $ Int 32 size, [])] [] []
  , nameAddress := AST.BitCast (LocalReference voidPointer varName) (pointer t) []
  ] ++ compileFields env supply' fields (LocalReference (pointer t) nameAddress) header headerBits
  where
    (nameAddress, supply') = freshName supply
    t = NamedTypeReference (toName conId)
    fields :: [(ConstructorFieldLayout, (Operand, Operand))]
    fields = zip fieldLayouts args
    headerBits :: Word32
    headerBits = fromIntegral headerSize * fromIntegral (targetPointerSize $ envTarget env)
    header :: Operand
    header = ConstantOperand $ Int headerBits $ Bits.shift (fromIntegral tag) firstTagBit
    size :: Integer
    size = fromIntegral $ constructorSize (envTarget env) layout

-- TODO: Add alignment to Store operations
compileFields :: Env -> NameSupply -> [(ConstructorFieldLayout, (Operand, Operand))] -> Operand -> Operand -> Word32 -> [Named Instruction]
compileFields env supply ((ConstructorFieldLayout _ index headerIndex, (operandValue, operandIsWHNF)) : rest) address header headerBits =
  [ elemPtr := getElementPtr address [0, index]
  , Do $ Store False (LocalReference voidPointer elemPtr) operandValue Nothing 0 []
  -- TODO: When we add strict fields, we must use the real type of the field instead of `voidPointer`.
  ]
  ++ case headerIndex of
    Nothing -> compileFields env supply' rest address header headerBits
    Just i ->
      -- Put `operandIsWHNF` in the ith bit of the header.
      -- shifted = isWHNF << i
      [ shifted := AST.Shl False False operandIsWHNF (ConstantOperand $ Int headerBits (fromIntegral i)) []
      -- header = header | shifted
      , newHeaderName := AST.Or header (LocalReference headerType shifted) []
      ]
      ++ compileFields env supply''' rest address (LocalReference headerType newHeaderName) headerBits
  where
    (elemPtr, supply') = freshName supply
    (shifted, supply'') = freshName supply'
    (newHeaderName, supply''') = freshName supply''
    headerType = IntegerType headerBits

-- All fields are processed, now put the header into the object
compileFields env supply [] address header headerBits =
  [ headerPtr := getElementPtr address [0, 0]
  , Do $ Store False (LocalReference (pointer $ IntegerType headerBits) headerPtr) (LocalReference (IntegerType headerBits) headerPtr) Nothing 0 []
  ]
  where
    (headerPtr, supply') = freshName supply
    t = IntegerType $ fromIntegral headerBits

compileExtractFields :: Env -> NameSupply -> Operand -> Word32 -> [ConstructorFieldLayout] -> [Id] -> [Named Instruction]
compileExtractFields env supply address headerBits layouts vars
  = [ headerPtr := getElementPtr address [0, 0]
    , headerName := Load False (LocalReference (pointer $ IntegerType headerBits) headerPtr) Nothing 0 []
    ]
    ++ extractInstructions
    
  where
    (headerPtr, supply') = freshName supply
    (headerName, supply'') = freshName supply'
    extractInstructions = concat
      $ mapWithSupply (\s (layout, varId) -> compileExtractField env s address (LocalReference (IntegerType headerBits) headerName) headerBits layout varId) supply''
      $ zip layouts vars

compileExtractField :: Env -> NameSupply -> Operand -> Operand -> Word32 -> ConstructorFieldLayout -> Id -> [Named Instruction]
compileExtractField env supply address header headerBits (ConstructorFieldLayout primType index Nothing) varId =
  [ namePtr := getElementPtr address [0, index]
  , toName varId := Load False (LocalReference (pointer t) namePtr) Nothing 0 []
  ]
  where
    (namePtr, supply') = freshName supply
    t = compileType env primType
compileExtractField env supply address header headerBits (ConstructorFieldLayout primType index (Just headerIndex)) varId =
  [ namePtr := getElementPtr address [0, index]
  , value := Load False (LocalReference voidPointer namePtr) Nothing 0 []
  , shifted := AST.LShr False header (ConstantOperand $ Int headerBits $ fromIntegral headerIndex) []
  , isWHNF := AST.Trunc (LocalReference (IntegerType headerBits) shifted) bool []
  , toName varId := AST.BitCast (ConstantOperand struct) taggedThunkPointer []
  , Do $ AST.InsertValue structRef (LocalReference voidPointer value) [0] []
  , Do $ AST.InsertValue structRef (LocalReference bool isWHNF) [1] []
  ]
  where
    (namePtr, supply') = freshName supply
    (value, supply'') = freshName supply'
    (shifted, supply''') = freshName supply''
    (isWHNF, supply'''') = freshName supply'''
    structRef = LocalReference taggedThunkPointer $ toName varId
    struct :: Constant
    struct = Struct Nothing True [Constant.Undef voidPointer, Constant.Undef bool]
