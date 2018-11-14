module Helium.CodeGeneration.LLVM.Builtins (builtinDefinitions, eval, alloc, unpackString) where

import Helium.CodeGeneration.LLVM.CompileType (pointer, voidPointer, bool)
import LLVM.AST
import LLVM.AST.Type
import LLVM.AST.Constant
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import Lvm.Common.Id(Id, stringFromId)

data Builtin = Builtin Name [Type] Type

builtin :: String -> [Type] -> Type -> Builtin
builtin = Builtin . mkName

eval', alloc', unpackString' :: Builtin
eval' = builtin "_$helium_runtime_eval" [voidPointer, IntegerType 64] voidPointer
-- Alignment, size (number of bytes)
alloc' = builtin "malloc" [IntegerType 32] voidPointer
-- Size, pointer to character (i32) array
-- TODO: use target pointer size
unpackString' = builtin "_$helium_runtime_unpack_string" [IntegerType 64, pointer $ IntegerType 8] (NamedTypeReference $ mkName "$data_[]")

builtins :: [Builtin]
builtins = [eval', alloc', unpackString']

builtinDefinitions :: [Definition]
builtinDefinitions = map definition builtins

eval, alloc, unpackString :: Operand
eval = operand eval'
alloc = operand alloc'
unpackString = operand unpackString'

operand :: Builtin -> Operand
operand (Builtin name args ret) = ConstantOperand $ GlobalReference (pointer t) name
  where
    t = FunctionType ret args False

definition :: Builtin -> Definition
definition (Builtin name args ret) = GlobalDefinition $ Function
  { Global.linkage = External
  , Global.visibility = Default
  , Global.dllStorageClass = Nothing
  , Global.callingConvention = C
  , Global.returnAttributes = []
  , Global.returnType = ret
  , Global.name = name
  , Global.parameters = (parameters, {- varargs: -} False)
  , Global.functionAttributes = []
  , Global.section = Nothing
  , Global.comdat = Nothing
  , Global.alignment = 0
  , Global.garbageCollectorName = Nothing
  , Global.prefix = Nothing
  , Global.basicBlocks = []
  , Global.personalityFunction = Nothing
  , Global.metadata = []
  }
  where
    parameters :: [Parameter]
    parameters = map (\t -> Parameter t (mkName "_") []) args
