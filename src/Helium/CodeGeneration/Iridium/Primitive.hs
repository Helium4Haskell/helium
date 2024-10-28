{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Primitive operations

module Helium.CodeGeneration.Iridium.Primitive(Primitive(..), primitives, findPrimitive) where

import Helium.Lvm.Common.Id(Id, idFromString, NameSupply)
import Helium.Lvm.Common.IdMap(IdMap, mapFromList, findMap)
import Helium.Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Utils

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
prim name args ret comp = (idFromString name, Primitive (FunctionType (map Right args) $ typeNotStrict ret) comp)

prim' :: String -> [Quantor] -> [Type] -> Type -> PrimitiveCompiler -> (Id, Primitive)
prim' name quantors args ret comp = (idFromString name, Primitive (FunctionType (map Left quantors ++ map Right args) $ typeNotStrict ret) comp)

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
primCompare name t g = prim' name [Quantor $ Just "a"] [t, t, TVar 0, TVar 0] (TVar 0) f
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

int16Type :: LLVM.Type
int16Type = LLVM.IntegerType 16

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

  -- New thunk evaluation
  , prim "thunk_extract_remaining" [typeUnsafePtr] typeInt16 $ compileThunkExtract 3
  , prim "thunk_extract_given" [typeUnsafePtr] typeInt16 $ compileThunkExtract 4
  , prim "thunk_extract_target" [typeUnsafePtr] typeUnsafePtr $ compileThunkExtract 1
  , prim "thunk_extract_value" [typeUnsafePtr] typeUnsafePtr $ compileThunkExtract 2
  -- Returns 0 when the thunk is undersaturated, 1 when it is saturated,
  -- 2 when it is oversaturated, but its target is not saturated,
  -- 3 when it is oversaturated, and its target is (over)saturated
  , prim "thunk_get_type" [typeInt, typeInt] typeInt compileThunkGetType
  , prim "thunk_eval" [typeUnsafePtr, typeInt16] typeUnsafePtr compileThunkEval
  , prim "thunk_eval_oversaturated_self" [typeUnsafePtr, typeInt16, typeInt16] typeUnsafePtr compileThunkOversaturatedSelf
  , prim "thunk_alloc_copy" [typeInt16, typeUnsafePtr] typeUnsafePtr compileThunkAllocCopy
  , prim "thunk_write" [typeUnsafePtr, typeInt, typeUnsafePtr, typeUnsafePtr, typeInt16, typeInt16] typeUnsafePtr compileThunkWrite
  , prim "thunk_write_value" [typeUnsafePtr, typeUnsafePtr] typeUnsafePtr compileThunkWriteValue

  , prim "int16_neg" [typeInt16] typeInt16
    $ \_ _ [operand] name -> [name LLVM.:= LLVM.Sub False False (LLVM.ConstantOperand $ LLVMConstant.Int 16 0) operand []]
  , prim "int16_add" [typeInt16, typeInt16] typeInt16
    $ \_ _ [left, right] name -> [name LLVM.:= LLVM.Add False False left right []]

  -- Conversion
  , prim "float64_to_int" [typeFloat] typeInt $ compileConversion LLVM.FPToSI (\target -> LLVM.IntegerType $ fromIntegral $ targetWordSize target)
  , prim "int_to_float64" [typeInt] typeFloat $ compileConversion LLVM.SIToFP $ const $ LLVM.FloatingPointType LLVM.DoubleFP
  , prim "int_to_char" [typeInt] typeChar $ compileConversion LLVM.BitCast (\target -> LLVM.IntegerType $ fromIntegral $ targetWordSize target)
  , prim "char_to_int" [typeInt] typeChar $ compileConversion LLVM.BitCast (\target -> LLVM.IntegerType $ fromIntegral $ targetWordSize target)
  , prim "int16_sext_to_int" [typeInt16] typeInt $ compileConversion LLVM.SExt (\target -> LLVM.IntegerType $ fromIntegral $ targetWordSize target)
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

compileThunkEval :: PrimitiveCompiler
compileThunkEval target supply [thunkVoid, given] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , nameFnPtrPtr LLVM.:= getElementPtr operandThunk [0, 2]
  , nameRemainingPtr LLVM.:= getElementPtr operandThunk [0, 3]
  -- Write 32767 to denote that the thunk is being evaluated
  , LLVM.Do $ LLVM.Store False operandRemainingPtr (LLVM.ConstantOperand $ LLVMConstant.Int 16 32767) Nothing 0 []
  -- Find the function pointer
  , nameFnPtr LLVM.:= LLVM.Load False operandFnPtrPtr Nothing 0 []
  -- Find the pointer to the first argument
  , nameFirstArgument LLVM.:= getElementPtr operandThunk [0, 5, 0]
  -- Call the function pointer
  , name LLVM.:= LLVM.Call
    { LLVM.tailCallKind = Nothing
    , LLVM.callingConvention = LLVM.Fast
    , LLVM.returnAttributes = []
    , LLVM.function = Right $ LLVM.LocalReference trampolineType nameFnPtr
    , LLVM.arguments =
      [ (operandThunk, [])
      , (LLVM.LocalReference (pointer taggedThunkPointer) nameFirstArgument, [])
      , (given, [])
      ]
    , LLVM.functionAttributes = []
    , LLVM.metadata = []
    }
  -- Write 32766 to denote that the thunk is evaluated
  , LLVM.Do $ LLVM.Store False operandRemainingPtr (LLVM.ConstantOperand $ LLVMConstant.Int 16 32766) Nothing 0 []
  -- Write result back to the thunk
  , nameValuePtr LLVM.:= LLVM.BitCast operandFnPtrPtr (pointer voidPointer) []
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer voidPointer) nameValuePtr) (LLVM.LocalReference voidPointer name) Nothing 0 []
  ]
  where
    operandThunk = LLVM.LocalReference thunkType nameThunk
    operandRemainingPtr = LLVM.LocalReference (pointer int16Type) nameRemainingPtr
    operandFnPtrPtr = LLVM.LocalReference (pointer trampolineType) nameFnPtrPtr
    (nameThunk, supply1) = freshName supply
    (nameRemainingPtr, supply2) = freshName supply1
    (nameFnPtrPtr, supply3) = freshName supply2
    (nameFnPtr, supply4) = freshName supply3
    (nameFirstArgument, supply5) = freshName supply4
    (nameValuePtr, _) = freshName supply5

compileThunkOversaturatedSelf :: PrimitiveCompiler
compileThunkOversaturatedSelf target supply [thunkVoid, argumentCount, argumentLast] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , nameFnPtrPtr LLVM.:= getElementPtr operandThunk [0, 2]
  , nameRemainingPtr LLVM.:= getElementPtr operandThunk [0, 3]
  -- Write 32767 to denote that the thunk is being evaluated
  , LLVM.Do $ LLVM.Store False operandRemainingPtr (LLVM.ConstantOperand $ LLVMConstant.Int 16 32767) Nothing 0 []
  -- Find the function pointer
  , nameFnPtr LLVM.:= LLVM.Load False operandFnPtrPtr Nothing 0 []
  -- Find the pointer to the last argument
  , nameLastArgument LLVM.:= LLVM.GetElementPtr False operandThunk
    [LLVM.ConstantOperand $ LLVMConstant.Int 32 0, LLVM.ConstantOperand $ LLVMConstant.Int 32 5, argumentLast]
    []
  -- Call the function pointer
  , name LLVM.:= LLVM.Call
    { LLVM.tailCallKind = Nothing
    , LLVM.callingConvention = LLVM.Fast
    , LLVM.returnAttributes = []
    , LLVM.function = Right $ LLVM.LocalReference trampolineType nameFnPtr
    , LLVM.arguments =
      [ (operandThunk, [])
      , (LLVM.LocalReference (pointer taggedThunkPointer) nameLastArgument, [])
      , (argumentCount, [])
      ]
    , LLVM.functionAttributes = []
    , LLVM.metadata = []
    }
  ]
  where
    operandThunk = LLVM.LocalReference thunkType nameThunk
    operandRemainingPtr = LLVM.LocalReference (pointer int16Type) nameRemainingPtr
    operandFnPtrPtr = LLVM.LocalReference (pointer trampolineType) nameFnPtrPtr
    (nameThunk, supply1) = freshName supply
    (nameRemainingPtr, supply2) = freshName supply1
    (nameFnPtrPtr, supply3) = freshName supply2
    (nameFnPtr, supply4) = freshName supply3
    (nameLastArgument, _) = freshName supply4

-- Updates a thunk after evaluating its target / next thunk.
compileThunkUpdateTarget :: PrimitiveCompiler
compileThunkUpdateTarget target supply [thunkVoid, targetVoid, given] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , nameTargetThunk LLVM.:= LLVM.BitCast targetVoid thunkType []

  -- Find pointers to function pointer and remaining of both thunks
  , nameThunkFnPtrPtr LLVM.:= getElementPtr operandThunk [0, 2]
  , nameThunkRemainingPtr LLVM.:= getElementPtr operandThunk [0, 3]
  , nameThunkNextPtr LLVM.:= getElementPtr operandThunk [0, 1]
  , nameTargetFnPtrPtr LLVM.:= getElementPtr operandTarget [0, 2]
  , nameTargetRemainingPtr LLVM.:= getElementPtr operandTarget [0, 3]

  -- Read from target
  , nameTargetFnPtr LLVM.:= LLVM.Load False (LLVM.LocalReference (pointer trampolineType) nameTargetFnPtrPtr) Nothing 0 []
  , nameTargetRemaining LLVM.:= LLVM.Load False (LLVM.LocalReference (pointer int16Type) nameTargetRemainingPtr) Nothing 0 []

  -- Compute new 'remaining'
  , nameRemaining LLVM.:= LLVM.Sub False False (LLVM.LocalReference int16Type nameTargetRemaining) given []

  -- Write new 'remaining', 'next' and function pointer
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer trampolineType) nameThunkFnPtrPtr) (LLVM.LocalReference trampolineType nameTargetFnPtr) Nothing 0 []
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer thunkType) nameThunkNextPtr) (LLVM.LocalReference thunkType nameTargetThunk) Nothing 0 []
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer int16Type) nameThunkRemainingPtr) (LLVM.LocalReference int16Type nameRemaining) Nothing 0 []
  ]
  where
    (nameThunk, supply1) = freshName supply
    (nameTargetThunk, supply2) = freshName supply1
    (nameThunkFnPtrPtr, supply3) = freshName supply2
    (nameThunkRemainingPtr, supply4) = freshName supply3
    (nameThunkNextPtr, supply5) = freshName supply4
    (nameTargetFnPtrPtr, supply6) = freshName supply5
    (nameTargetRemainingPtr, supply7) = freshName supply6
    (nameTargetFnPtr, supply8) = freshName supply7
    (nameTargetRemaining, supply9) = freshName supply8
    (nameRemaining, _) = freshName supply9

    operandThunk = LLVM.LocalReference thunkType nameThunk
    operandTarget = LLVM.LocalReference thunkType nameTargetThunk

compileThunkExtract :: Int -> PrimitiveCompiler
compileThunkExtract index target supply [thunkVoid] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , namePtr LLVM.:= getElementPtr (LLVM.LocalReference thunkType nameThunk) [0, index]
  , nameLoad LLVM.:= LLVM.Load False (LLVM.LocalReference (pointer tp) namePtr) Nothing 0 []
  ] ++ bitcast
  where
    (nameThunk, supply1) = freshName supply
    (namePtr, supply2) = freshName supply1
    (nameBeforeCast, _) = freshName supply2
    (tp, bitcast, nameLoad) = case index of
      1 -> -- Target
        ( thunkType
        , [ name LLVM.:= LLVM.BitCast (LLVM.LocalReference thunkType nameBeforeCast) voidPointer [] ]
        , nameBeforeCast
        )
      2 -> -- Function or evaluated value
        ( trampolineType
        , [ name LLVM.:= LLVM.BitCast (LLVM.LocalReference trampolineType nameBeforeCast) voidPointer [] ]
        , nameBeforeCast
        )
      _ -> (int16Type, [], name) -- remaining or given

-- Returns 0 when the thunk is undersaturated, 1 when it is saturated,
-- 2 when it is oversaturated, but its target is not saturated,
-- 3 when it is oversaturated, and its target is (over)saturated
compileThunkGetType :: PrimitiveCompiler
compileThunkGetType target supply [remaining, given] name =
  -- Thunk is in WHNF (type 0) if remaining > 0
  [ nameWhnf LLVM.:= LLVM.ICmp IntegerPredicate.SGT remaining (LLVM.ConstantOperand $ LLVMConstant.Int 16 0) []
  -- Thunk is exactly saturated (type 1) if remaining == 0
  , nameSaturated LLVM.:= LLVM.ICmp IntegerPredicate.EQ remaining (LLVM.ConstantOperand $ LLVMConstant.Int 16 0) []
  -- Thunk is oversaturated, and the target not saturated (type 2), if remaining < 0 and -remaining < given
  , nameMinusRemaining LLVM.:= LLVM.Sub False False (LLVM.ConstantOperand $ LLVMConstant.Int 16 0) remaining []
  , nameOversaturatedSelf LLVM.:= LLVM.ICmp IntegerPredicate.SLT (LLVM.LocalReference int16Type nameMinusRemaining) given []
  , name23 LLVM.:= LLVM.Select (boolOperand nameOversaturatedSelf) (constant 2) (constant 3) []
  , name123 LLVM.:= LLVM.Select (boolOperand nameSaturated) (constant 1) (typeOperand name23) []
  , name LLVM.:= LLVM.Select (boolOperand nameWhnf) (constant 0) (typeOperand name123) []
  ]
  where
    boolOperand = LLVM.LocalReference (LLVM.IntegerType 1)
    typeOperand = LLVM.LocalReference $ LLVM.IntegerType $ fromIntegral $ targetWordSize target
    constant = LLVM.ConstantOperand . LLVMConstant.Int (fromIntegral $ targetWordSize target) . fromIntegral
    (nameWhnf, supply1) = freshName supply
    (nameSaturated, supply2) = freshName supply1
    (nameMinusRemaining, supply3) = freshName supply2
    (nameOversaturatedSelf, supply4) = freshName supply3
    (name23, supply5) = freshName supply4
    (name123, _) = freshName supply5

compileThunkAllocCopy :: PrimitiveCompiler
compileThunkAllocCopy target supply [fieldCount, base] name =
  [ nameFieldSize LLVM.:= LLVM.Mul False False fieldCount (LLVM.ConstantOperand $ LLVMConstant.Int 16 $ fromIntegral $ (targetWordSize target `div` 8) + 1) []
  , nameSize LLVM.:= LLVM.Add False False (LLVM.LocalReference int16Type nameFieldSize) (LLVM.ConstantOperand $ LLVMConstant.Int 16 $ fromIntegral $ (targetWordSize target * 3 `div` 8) + 4) []
  , nameSize32 LLVM.:= LLVM.ZExt (LLVM.LocalReference (LLVM.IntegerType 16) nameSize) (LLVM.IntegerType 32) []
  , name LLVM.:= LLVM.Call
    { LLVM.tailCallKind = Nothing
    , LLVM.callingConvention = LLVM.C
    , LLVM.returnAttributes = []
    , LLVM.function = Right $ LLVM.ConstantOperand $ LLVMConstant.GlobalReference (pointer $ LLVM.FunctionType typeVoidPtr [int16Type] False) $ LLVM.mkName "helium_global_alloc"
    , LLVM.arguments =
      [ (LLVM.LocalReference (LLVM.IntegerType 32) nameSize32, []) ]
    , LLVM.functionAttributes = []
    , LLVM.metadata = []
    }
  , LLVM.Do $ LLVM.Call
    { LLVM.tailCallKind = Nothing
    , LLVM.callingConvention = LLVM.C
    , LLVM.returnAttributes = []
    , LLVM.function = Right $ LLVM.ConstantOperand $ LLVMConstant.GlobalReference (pointer $ LLVM.FunctionType typeVoidPtr [int16Type] False) $ LLVM.mkName "memcpy"
    , LLVM.arguments =
      [ (LLVM.LocalReference voidPointer name, [])
      , (base, [])
      , (LLVM.LocalReference (LLVM.IntegerType 32) nameSize32, [])
      ]
    , LLVM.functionAttributes = []
    , LLVM.metadata = []
    }
  ]
  where
    (nameFieldSize, supply') = freshName supply
    (nameSize, supply'') = freshName supply'
    (nameSize32, _) = freshName supply''

compileThunkWrite :: PrimitiveCompiler
compileThunkWrite buildTarget supply [thunkVoid, header, target, fn, remaining, given] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , getPointer nameHeader [0, 0]
  , getPointer nameTarget [0, 1]
  , getPointer nameFn [0, 2]
  , getPointer nameRemaining [0, 3]
  , getPointer nameGiven [0, 4]

  , target' LLVM.:= LLVM.BitCast target thunkType []
  , fn' LLVM.:= LLVM.BitCast fn trampolineType []

  , store nameHeader header $ LLVM.IntegerType $ fromIntegral $ targetWordSize buildTarget
  , store nameTarget (LLVM.LocalReference thunkType target') thunkType
  , store nameFn (LLVM.LocalReference trampolineType fn') trampolineType
  , store nameRemaining remaining int16Type
  , store nameGiven given int16Type
  ]
  where
    getPointer namePtr indices = namePtr LLVM.:= getElementPtr (LLVM.LocalReference thunkType nameThunk) indices
    store namePtr operandValue tp =
      LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer tp) namePtr) operandValue Nothing 0 []
    (nameThunk, supply0) = freshName supply
    (nameHeader, supply1) = freshName supply0
    (nameTarget, supply2) = freshName supply1
    (nameFn, supply3) = freshName supply2
    (nameRemaining, supply4) = freshName supply3
    (nameGiven, supply5) = freshName supply4
    (target', supply6) = freshName supply5
    (fn', _) = freshName supply6

compileThunkWriteValue :: PrimitiveCompiler
compileThunkWriteValue buildTarget supply [thunkVoid, value] name =
  [ nameThunk LLVM.:= LLVM.BitCast thunkVoid thunkType []
  , getPointer nameFn [0, 2]
  , getPointer nameRemaining [0, 3]

  , nameValue LLVM.:= LLVM.BitCast (LLVM.LocalReference (pointer trampolineType) nameFn) (pointer voidPointer) []

  , store nameValue value voidPointer
  , store nameRemaining (LLVM.ConstantOperand $ LLVMConstant.Int 16 32766) int16Type
  ]
  where
    getPointer namePtr indices = namePtr LLVM.:= getElementPtr (LLVM.LocalReference thunkType nameThunk) indices
    store namePtr operandValue tp =
      LLVM.Do $ LLVM.Store False (LLVM.LocalReference (pointer tp) namePtr) operandValue Nothing 0 []
    (nameThunk, supply0) = freshName supply
    (nameFn, supply1) = freshName supply0
    (nameRemaining, supply2) = freshName supply1
    (nameValue, _) = freshName supply2

compileConversion :: (LLVM.Operand -> LLVM.Type -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Target -> LLVM.Type) -> PrimitiveCompiler
compileConversion instr ty target _ [arg] name =
  [ name LLVM.:= instr arg (ty target) []
  ]
