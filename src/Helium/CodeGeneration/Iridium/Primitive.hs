{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Primitive operations

module Helium.CodeGeneration.Iridium.Primitive(Primitive(..), primitives, findPrimitive) where

import Lvm.Common.Id(Id, idFromString, NameSupply)
import Lvm.Common.IdMap(IdMap, mapFromList, findMap)
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Utils(freshName, getElementPtr)

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Instruction as LLVM
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate
import qualified LLVM.AST.FloatingPointPredicate as FloatingPointPredicate
import qualified LLVM.AST.AddrSpace as LLVM
import qualified LLVM.AST.CallingConvention as LLVM
import qualified LLVM.AST.Constant as LLVMConstant

type PrimitiveCompiler = Target -> NameSupply -> [LLVM.Operand] -> LLVM.Name -> [LLVM.Named LLVM.Instruction]

data Primitive = Primitive
  { primType :: FunctionType
  , primCompile :: PrimitiveCompiler
  }

prim :: String -> [Type] -> Type -> PrimitiveCompiler -> (Id, Primitive)
prim name args ret comp = (idFromString name, Primitive (FunctionType (map Right args) ret) comp)

prim' :: String -> [Quantor] -> [Type] -> Type -> PrimitiveCompiler -> (Id, Primitive)
prim' name quantors args ret comp = (idFromString name, Primitive (FunctionType (map Left quantors ++ map Right args) ret) comp)

primBinaryInt :: String -> (LLVM.Operand -> LLVM.Operand -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Id, Primitive)
primBinaryInt name g = prim name [typeInt, typeInt] typeInt f
  where
    f _ _ [a, b] var = [var LLVM.:= g a b []]
    f _ _ _ _ = error "expected two arguments for binary int primitive"

primBinaryDouble :: String -> (LLVM.Operand -> LLVM.Operand -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Id, Primitive)
primBinaryDouble name g = prim name [typeFloat, typeFloat] (typeFloat) f
  where
    f _ _ [a, b] var = [var LLVM.:= g a b []]
    f _ _ _ _ = error "expected two arguments for binary double primitive"

primCompare :: String -> Type -> (LLVM.Operand -> LLVM.Operand -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Id, Primitive)
primCompare name t g = prim' name [Quantor 0 $ Just "a"] [t, t, TVar 0, TVar 0] (TVar 0) f
  where
    f target supply [a, b, whenTrue, whenFalse] var =
      [ bool LLVM.:= g a b []
      , var LLVM.:= LLVM.Select (LLVM.LocalReference (LLVM.IntegerType 1) bool) whenTrue whenFalse []
      ]
      where
        (bool, _) = freshName supply

primitives :: IdMap Primitive
primitives = mapFromList primitiveList

fastMathFlagsNone :: LLVM.FastMathFlags
fastMathFlagsNone = LLVM.FastMathFlags False False False False False False False

primitiveList :: [(Id, Primitive)]
primitiveList =
  [ primBinaryInt "int_add" $ LLVM.Add False False
  , primBinaryInt "int_sub" $ LLVM.Sub False False
  , primBinaryInt "int_mul" $ LLVM.Mul False False
  -- Note: rounds to zero, whereas `div` in Haskell rounds to -inf
  -- This thus maps to `quot` in haskell.
  , primBinaryInt "int_sdiv" $ LLVM.SDiv False
  , primBinaryInt "int_srem" LLVM.SRem

  , primBinaryInt "int_and" LLVM.And
  , primBinaryInt "int_or" LLVM.Or
  , primBinaryInt "int_xor" LLVM.Xor
  , primBinaryInt "int_shl" $ LLVM.Shl False False
  , primBinaryInt "int_lshr" $ LLVM.LShr False -- Logical right shift
  , primBinaryInt "int_ashr" $ LLVM.AShr False -- Arithmetic right shift

  , primCompare "int_eq" typeInt $ LLVM.ICmp IntegerPredicate.EQ
  , primCompare "int_slt" typeInt $ LLVM.ICmp IntegerPredicate.SLT -- Signed less than

  -- Float arithmetics
  , primBinaryDouble "float64_add" $ LLVM.FAdd fastMathFlagsNone
  , primBinaryDouble "float64_sub" $ LLVM.FSub fastMathFlagsNone
  , primBinaryDouble "float64_mul" $ LLVM.FMul fastMathFlagsNone
  , primBinaryDouble "float64_div" $ LLVM.FDiv fastMathFlagsNone

  -- Float comparisons
  , primCompare "float64_eq" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.OEQ
  , primCompare "float64_ne" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.ONE
  , primCompare "float64_gt" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.OGT
  , primCompare "float64_lt" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.OLT
  , primCompare "float64_ge" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.OGE
  , primCompare "float64_le" (typeFloat) $ LLVM.FCmp FloatingPointPredicate.OLE

  , prim "unsafeptr_add" [typeUnsafePtr, typeInt] typeUnsafePtr compilePtrAdd
  -- Reads a 32 bit integer
  , prim "unsafeptr_read32" [typeUnsafePtr] typeInt compileRead32
  , prim "unsafeptr_read" [typeUnsafePtr] typeUnsafePtr compileRead
  , prim' "unsafeptr_write" [Quantor 0 $ Just "a"] [typeUnsafePtr, TVar 0] typeInt compileWrite

  , prim "thunk_extract_tag" [typeUnsafePtr] typeInt compileThunkExtractTag
  , prim "thunk_target_ptr_offset" [typeInt] typeInt compileThunkTargetOffset
  , prim "thunk_write_tag" [typeUnsafePtr, typeInt] typeInt compileThunkWriteTag
  , prim' "thunk_call" [Quantor 0 $ Just "a"] [typeUnsafePtr, typeUnsafePtr] (TVar 0) compileThunkCall

  -- Conversion
  , prim "float64_to_int" [typeFloat] typeInt $ compileConversion LLVM.FPToSI (\target -> LLVM.IntegerType $ fromIntegral $ targetWordSize target)
  , prim "int_to_float64" [typeInt] (typeFloat) $ compileConversion LLVM.SIToFP $ const $ LLVM.FloatingPointType LLVM.DoubleFP
  ]

findPrimitive :: Id -> Primitive
findPrimitive = (`findMap` primitives)

compilePtrAdd :: PrimitiveCompiler
compilePtrAdd _ _  [pointer, inc] name = [ name LLVM.:= LLVM.GetElementPtr False pointer [inc] [] ]

compileRead32 :: PrimitiveCompiler
compileRead32 target supply [pointer] name =
  [ namePtr LLVM.:= LLVM.BitCast pointer ptrType []
  , (if is32Bit then name else nameValue) LLVM.:= LLVM.Load False (LLVM.LocalReference ptrType namePtr) Nothing 0 []
  ] ++ if is32Bit then [] else
    [ name LLVM.:= LLVM.ZExt (LLVM.LocalReference (LLVM.IntegerType 32) nameValue) (LLVM.IntegerType $ fromIntegral $ targetWordSize target) [] ]
  where
    ptrType = LLVM.PointerType (LLVM.IntegerType 32) (LLVM.AddrSpace 0)
    (namePtr, supply') = freshName supply
    (nameValue, _) = freshName supply'
    is32Bit = targetWordSize target == 32

typeVoidPtr :: LLVM.Type
typeVoidPtr = LLVM.PointerType (LLVM.IntegerType 8) (LLVM.AddrSpace 0)
typeVoidPtrPtr = LLVM.PointerType typeVoidPtr (LLVM.AddrSpace 0)

compileRead :: PrimitiveCompiler
compileRead _ supply [pointer] name =
  [ namePtr LLVM.:= LLVM.BitCast pointer typeVoidPtrPtr []
  , name LLVM.:= LLVM.Load False (LLVM.LocalReference typeVoidPtrPtr namePtr) Nothing 0 []
  ]
  where
    (namePtr, _) = freshName supply

compileWrite :: PrimitiveCompiler
compileWrite _ supply [pointer, value] name =
  [ namePtr LLVM.:= LLVM.BitCast pointer typeVoidPtrPtr []
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference typeVoidPtrPtr namePtr) value Nothing 0 []
  ]
  where
    (namePtr, _) = freshName supply

compileThunkExtractTag :: PrimitiveCompiler
compileThunkExtractTag target supply [pointer] name =
  [ namePtr LLVM.:= LLVM.BitCast pointer ptrType []
  , nameElementPtr LLVM.:= getElementPtr (LLVM.LocalReference ptrType namePtr) [if is32Bit then 2 else 1]
  , (if is32Bit then name else nameValue) LLVM.:= LLVM.Load False (LLVM.LocalReference ptrType nameElementPtr) Nothing 0 []
  ] ++ if is32Bit then [] else
    [ name LLVM.:= LLVM.And (LLVM.LocalReference intType nameValue) (LLVM.ConstantOperand $ LLVMConstant.Int (fromIntegral wordSize) 0xFFFFFFFF) [] ]
  where
    intType = LLVM.IntegerType $ fromIntegral wordSize
    ptrType = LLVM.PointerType intType (LLVM.AddrSpace 0)
    wordSize = targetWordSize target
    is32Bit = wordSize == 32
    (namePtr, supply') = freshName supply
    (nameElementPtr, supply'') = freshName supply'
    (nameValue, _) = freshName supply''

-- Result value is not defined for this construct. 
compileThunkWriteTag :: PrimitiveCompiler
compileThunkWriteTag target supply [pointer, value] name
  | wordSize == 32 =
    [ namePtr LLVM.:= LLVM.BitCast pointer ptrType []
    , nameElementPtr LLVM.:= getElementPtr (LLVM.LocalReference ptrType namePtr) [2]
    , LLVM.Do $ LLVM.Store False (LLVM.LocalReference ptrType nameElementPtr) value Nothing 0 []
    , name LLVM.:= LLVM.ZExt (LLVM.ConstantOperand $ LLVMConstant.Int 1 0) (LLVM.IntegerType $ fromIntegral $ targetWordSize target) []
    ]
  | wordSize == 64 =
    -- Put `value` in the 32 least significant bits of the second word of the thunk
    [ namePtr LLVM.:= LLVM.BitCast pointer ptrType []
    , nameElementPtr LLVM.:= getElementPtr (LLVM.LocalReference ptrType namePtr) [1]
    , nameValue LLVM.:= LLVM.Load False (LLVM.LocalReference ptrType nameElementPtr) Nothing 0 []
    , nameValueMasked LLVM.:= LLVM.And (LLVM.LocalReference intType nameValue) (LLVM.ConstantOperand $ LLVMConstant.Int (fromIntegral wordSize) 0xFFFFFFFF00000000) []
    -- The return value is not defined so we can actually use `name` as a temporary variable here
    , name LLVM.:= LLVM.Or (LLVM.LocalReference intType nameValueMasked) value []
    , LLVM.Do $ LLVM.Store False (LLVM.LocalReference ptrType nameElementPtr) (LLVM.LocalReference intType name) Nothing 0 []
    ]
  | otherwise = error "Helium.CodeGeneration.Iridum.Primitive.compileThunkWriteTag: unsupported word size"
  where
    wordSize = targetWordSize target
    intType = LLVM.IntegerType $ fromIntegral wordSize
    ptrType = LLVM.PointerType intType (LLVM.AddrSpace 0)
    (namePtr, supply1) = freshName supply
    (nameElementPtr, supply2) = freshName supply1
    (nameValue, supply3) = freshName supply2
    (nameValueMasked, _) = freshName supply3
  

-- Computes the offset of the target field (first field) of a thunk.
-- This depends on the number of arguments, as each field gets one bit in the header of the object.
-- The first words of the object contain GC information (48 bits) and a tag (32 bit, contains the
-- number of given arguments and the remaining arguments)
-- The number of header fields that we use for this "standard" bookkeeping depends on the word size
-- We call that defaultHeaderCount. There are some bits left in those fields, we call the number of
-- those bits flagsInFirstAndSecondWord
--
-- We want to compute the number of header words:
-- DEFAULT_HEADER_COUNT + ceil((argCount - FLAGS_IN_FIRST_AND_SECOND_WORD) / WORDSIZE)
-- We can replace that with:
-- DEFAULT_HEADER_COUNT + floor((argCount - FLAGS_IN_FIRST_AND_SECOND_WORD + WORDSIZE - 1) / WORDSIZE)
-- Now we can use the integer devision, as we round down. LLVM will replace the devision with a bitshift.
-- We also put the `DEFAULT_HEADER_COUNT + ` in the division, such that we only perform 2 instructions.
compileThunkTargetOffset :: PrimitiveCompiler
compileThunkTargetOffset target supply [argCount] name =
  [ nameNumerator LLVM.:= LLVM.Add False False argCount (LLVM.ConstantOperand $ LLVMConstant.Int (fromIntegral wordSize) $ fromIntegral $ wordSize - flagsInFirstAndSecondWord - 1 + defaultHeaderCount * wordSize) []
  , nameDivision LLVM.:= LLVM.UDiv False (LLVM.LocalReference intType nameNumerator) (LLVM.ConstantOperand $ LLVMConstant.Int (fromIntegral wordSize) $ fromIntegral wordSize) []
  -- Multiply as we index pointers to bytes (not words)
  , name LLVM.:= LLVM.Mul False False (LLVM.LocalReference intType nameDivision) (LLVM.ConstantOperand $ LLVMConstant.Int (fromIntegral wordSize) $ fromIntegral $ wordSize `div` 8) []
  ]
  where
    intType = LLVM.IntegerType $ fromIntegral wordSize
    wordSize = targetWordSize target
    (defaultHeaderCount, flagsInFirstAndSecondWord) = case wordSize of
      32 -> (3, 16)
      64 -> (2, 48)
    (nameNumerator, supply') = freshName supply
    (nameDivision, _) = freshName supply'

compileThunkCall :: PrimitiveCompiler
compileThunkCall target supply [fn, arg] name =
  [ nameFn LLVM.:= LLVM.BitCast fn fnType []
  , name LLVM.:= LLVM.Call 
    { LLVM.tailCallKind = Nothing
    , LLVM.callingConvention = LLVM.Fast
    , LLVM.returnAttributes = []
    , LLVM.function = Right $ LLVM.LocalReference fnType nameFn
    , LLVM.arguments =
      [ (arg, [])
      ]
    , LLVM.functionAttributes = []
    , LLVM.metadata = []
    }
  ]
  where
    fnType = LLVM.PointerType (LLVM.FunctionType typeVoidPtr [typeVoidPtr] False) (LLVM.AddrSpace 0)
    (nameFn, _) = freshName supply

compileConversion :: (LLVM.Operand -> LLVM.Type -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Target -> LLVM.Type) -> PrimitiveCompiler
compileConversion instr ty target _ [arg] name =
  [ name LLVM.:= instr arg (ty target) []
  ]
