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
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Utils(freshName)

import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Instruction as LLVM
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate
import qualified LLVM.AST.AddrSpace as LLVM
import qualified LLVM.AST.CallingConvention as LLVM

type PrimitiveCompiler = Target -> NameSupply -> [LLVM.Operand] -> LLVM.Name -> [LLVM.Named LLVM.Instruction]

data Primitive = Primitive
  { primArguments :: [PrimitiveType]
  , primReturn :: PrimitiveType
  , primCompile :: PrimitiveCompiler
  }

prim :: String -> [PrimitiveType] -> PrimitiveType -> PrimitiveCompiler -> (Id, Primitive)
prim name args ret comp = (idFromString name, Primitive args ret comp)

primBinaryInt :: String -> (LLVM.Operand -> LLVM.Operand -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Id, Primitive)
primBinaryInt name g = prim name [TypeInt, TypeInt] TypeInt f
  where
    f _ _ [a, b] var = [var LLVM.:= g a b []]
    f _ _ _ _ = error "expected two arguments for binary int primitive"

primCompare :: String -> PrimitiveType -> (LLVM.Operand -> LLVM.Operand -> LLVM.InstructionMetadata -> LLVM.Instruction) -> (Id, Primitive)
primCompare name t g = prim name [t, t] TypeInt f
  where
    f target supply [a, b] var =
      [ bool LLVM.:= g a b []
      , var LLVM.:= LLVM.ZExt (LLVM.LocalReference (LLVM.IntegerType 1) bool) (LLVM.IntegerType $ fromIntegral $ targetWordSize target) []
      ]
      where
        (bool, _) = freshName supply

primitives :: IdMap Primitive
primitives = mapFromList primitiveList

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
  , primBinaryInt "int_rshr" $ LLVM.AShr False -- Arithmetic right shift

  , primCompare "int_eq" TypeInt $ LLVM.ICmp IntegerPredicate.EQ
  , primCompare "int_slt" TypeInt $ LLVM.ICmp IntegerPredicate.SLT -- Signed less than

  , prim "unsafeptr_add" [TypeUnsafePtr, TypeInt] TypeUnsafePtr compilePtrAdd
  -- Reads a 32 bit integer
  , prim "unsafeptr_read32" [TypeUnsafePtr] TypeInt compileRead32
  , prim "unsafeptr_read" [TypeUnsafePtr] TypeAny compileRead
  , prim "unsafeptr_write" [TypeUnsafePtr, TypeAny] TypeInt compileWrite

  , prim "thunk_extract_tag" [TypeUnsafePtr] TypeInt undefined -- TODO
  , prim "thunk_target_ptr_offset" [TypeInt] TypeInt undefined -- TODO
  , prim "thunk_write_tag" [TypeUnsafePtr, TypeInt] TypeInt undefined -- TODO
  , prim "thunk_call" [TypeUnsafePtr, TypeUnsafePtr] TypeAny compileThunkCall
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
  [ namePtr LLVM.:= LLVM.BitCast pointer typeVoidPtr []
  , name LLVM.:= LLVM.Load False (LLVM.LocalReference typeVoidPtrPtr namePtr) Nothing 0 []
  ]
  where
    (namePtr, _) = freshName supply

compileWrite :: PrimitiveCompiler
compileWrite _ supply [pointer, value] name =
  [ namePtr LLVM.:= LLVM.BitCast pointer typeVoidPtr []
  , LLVM.Do $ LLVM.Store False (LLVM.LocalReference typeVoidPtrPtr namePtr) value Nothing 0 []
  ]
  where
    (namePtr, _) = freshName supply

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
