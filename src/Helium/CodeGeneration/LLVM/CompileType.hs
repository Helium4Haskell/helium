module Helium.CodeGeneration.LLVM.CompileType (compileType, toOperand, taggedThunkPointer, bool, pointer, voidPointer, splitValueFlag, cast) where

import Lvm.Common.Id(Id, freshId, stringFromId, NameSupply)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv
import LLVM.AST as AST
import LLVM.AST.Constant as Constant
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import LLVM.AST.Constant

compileType :: Env -> Iridium.PrimitiveType -> Type
compileType env Iridium.TypeAny = taggedThunkPointer
compileType env Iridium.TypeAnyThunk = voidPointer
compileType env Iridium.TypeAnyWHNF = voidPointer
compileType env Iridium.TypeInt = envValueType env
compileType env Iridium.TypeDouble = FloatingPointType DoubleFP
compileType env (Iridium.TypeDataType _) = voidPointer
compileType env Iridium.TypeFunction = voidPointer

compileFunctionType :: Env -> Iridium.FunctionType -> Type
compileFunctionType env (Iridium.FunctionType args returnType) = pointer $ FunctionType (compileType env returnType) (map (compileType env) args) False

bool :: Type
bool = IntegerType 1

-- Bool denotes whether the value is in WHNF
taggedThunkPointer :: Type
taggedThunkPointer = StructureType True [voidPointer, bool]

pointer :: Type -> Type
pointer t = Type.PointerType t (AddrSpace 0)

voidPointer :: Type
voidPointer = pointer (IntegerType 8)

toOperand :: Env -> Id -> Operand
toOperand env name = case TypeEnv.valueDeclaration (envTypeEnv env) name of
  (TypeEnv.ValueVariable prim) -> LocalReference (compileType env prim) (toName name)
  (TypeEnv.ValueFunction fntype) -> ConstantOperand $ GlobalReference (compileFunctionType env fntype) (toName name)

splitValueFlag :: Env -> NameSupply -> Id -> ([Named Instruction], (Operand, Operand))
splitValueFlag env supply name = case TypeEnv.valueDeclaration (envTypeEnv env) name of
  (TypeEnv.ValueVariable Iridium.TypeAnyWHNF) ->
    ( [ toName ptrValue := AST.GetElementPtr False (LocalReference taggedThunkPointer (toName name)) [ConstantOperand $ Int 8 0, ConstantOperand $ Int 8 0] []
      , toName ptrIsWHNF := AST.GetElementPtr False (LocalReference taggedThunkPointer (toName name)) [ConstantOperand $ Int 8 0, ConstantOperand $ Int 8 1] []
      , toName nameValue := Load False (LocalReference (pointer voidPointer) (toName ptrValue)) Nothing 0 []
      , toName nameIsWHNF := Load False (LocalReference (pointer bool) (toName ptrIsWHNF)) Nothing 0 []
      ]
    , ( LocalReference voidPointer (toName nameValue)
      , LocalReference bool (toName nameIsWHNF)
      )
    )
  (TypeEnv.ValueVariable Iridium.TypeAnyThunk) ->
    ( []
    , ( LocalReference voidPointer (toName name)
      , ConstantOperand $ Int 1 0 -- false
      )
    )
  (TypeEnv.ValueVariable t) ->
    ( []
    , (LocalReference (compileType env t) (toName name)
      , ConstantOperand $ Int 1 1 -- true
      )
    )
  where
    operand = LocalReference (compileType env Iridium.TypeAnyWHNF) (toName name)
    (ptrValue, supply') = freshId supply
    (ptrIsWHNF, supply'') = freshId supply'
    (nameValue, supply''') = freshId supply''
    (nameIsWHNF, _) = freshId supply'''

-- TODO: Casts from / to int or double
cast :: Env -> Name -> Name -> Iridium.PrimitiveType -> Iridium.PrimitiveType -> [Named Instruction]
cast env fromName toName Iridium.TypeAny Iridium.TypeAny = [toName := AST.BitCast (LocalReference taggedThunkPointer fromName) taggedThunkPointer []]
cast env fromName toName fromType Iridium.TypeAny =
  [ toName := AST.BitCast
      (ConstantOperand $ Struct Nothing True [Constant.Undef voidPointer, Constant.Int 1 (if fromType == Iridium.TypeAnyThunk then 0 else 1)])
      taggedThunkPointer
      []
  , Do $ AST.InsertValue (LocalReference taggedThunkPointer toName) (LocalReference voidPointer fromName) [1] []
  ]
cast env fromName toName fromType toType = [toName := AST.BitCast (LocalReference fromT fromName) fromT []]
  where
    fromT = compileType env fromType
