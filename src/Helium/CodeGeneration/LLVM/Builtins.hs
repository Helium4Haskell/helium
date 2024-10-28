module Helium.CodeGeneration.LLVM.Builtins (builtinDefinitions, eval, alloc, unpackString) where

import Helium.CodeGeneration.Iridium.Data as Iridium
import Helium.CodeGeneration.LLVM.Utils
import LLVM.AST
import LLVM.AST.Type
import LLVM.AST.Constant
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import Helium.Lvm.Common.Id(Id, stringFromId, idFromString)

data Builtin = Builtin Id [Type] Type

builtin :: String -> [Type] -> Type -> Builtin
builtin = Builtin . idFromString

eval', alloc', memcpy', unpackString' :: Builtin
eval' = builtin "_$helium_runtime_eval" [voidPointer, IntegerType 64] voidPointer
-- Alignment, size (number of bytes)
alloc' = builtin "helium_global_alloc" [IntegerType 32] voidPointer
memcpy' = builtin "memcpy" [voidPointer, voidPointer, IntegerType 32] voidPointer
-- Size, pointer to character (i32) array
-- TODO: use target pointer size
unpackString' = builtin "_$helium_runtime_unpack_string" [IntegerType 64, pointer $ IntegerType 8] voidPointer

builtins :: Iridium.Module -> [Builtin]
builtins iridium = filter (\(Builtin name _ _) -> not $ Iridium.declaresFunction iridium name) allBuiltins
  
allBuiltins :: [Builtin]
allBuiltins = [eval', alloc', memcpy', unpackString']

builtinDefinitions :: Iridium.Module -> [Definition]
builtinDefinitions iridium = map definition $ builtins iridium

eval, alloc, unpackString :: Operand
eval = operand eval'
alloc = operand alloc'
unpackString = operand unpackString'

operand :: Builtin -> Operand
operand (Builtin name args ret) = ConstantOperand $ GlobalReference (pointer t) $ toName name
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
  , Global.name = toName name
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
