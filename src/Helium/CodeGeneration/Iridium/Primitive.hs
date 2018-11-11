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
  ]

findPrimitive :: Id -> Primitive
findPrimitive = (`findMap` primitives)
