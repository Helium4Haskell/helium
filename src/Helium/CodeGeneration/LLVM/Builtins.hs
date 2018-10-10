module Helium.CodeGeneration.LLVM.Builtins (eval, alloc) where

import Helium.CodeGeneration.LLVM.CompileType (pointer, voidPointer, bool)
import LLVM.AST
import LLVM.AST.Type
import LLVM.AST.Constant
import Lvm.Common.Id(Id, stringFromId)

eval :: Operand
eval = ConstantOperand $ GlobalReference (pointer t) (mkName "_$helium_runtime_eval")
  where
    t = FunctionType voidPointer [voidPointer, bool] False

alloc :: Operand
alloc = ConstantOperand $ GlobalReference (pointer t) (mkName "_$helium_runtime_alloc")
  where
    -- Alignment, size (number of bytes)
    t = FunctionType voidPointer [IntegerType 32, IntegerType 32] False
