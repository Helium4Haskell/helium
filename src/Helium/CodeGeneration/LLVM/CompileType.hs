module Helium.CodeGeneration.LLVM.CompileType (compileType, toOperand, taggedThunkPointer, bool, pointer, voidPointer, splitValueFlag, cast) where

import Lvm.Common.Id(Id, freshId, stringFromId, NameSupply)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
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
compileType env (Iridium.TypeDataType dataName) = NamedTypeReference $ toNamePrefixed "$data_" dataName
compileType env Iridium.TypeFunction = voidPointer
compileType env (Iridium.TypeGlobalFunction fntype) = compileFunctionType env fntype

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

toOperand :: Env -> Iridium.Variable -> Operand
toOperand env (Iridium.VarLocal (Iridium.Local name t)) = LocalReference (compileType env t) (toName name)
toOperand env (Iridium.VarGlobal (Iridium.Global name fntype)) = ConstantOperand $ GlobalReference (compileFunctionType env fntype) (toName name)

splitValueFlag :: Env -> NameSupply -> Iridium.Variable -> ([Named Instruction], (Operand, Operand))
splitValueFlag env supply var = case Iridium.variableType var of
  Iridium.TypeAny ->
    ( [ nameValue := AST.ExtractValue operand [0] []
      , nameIsWHNF := AST.ExtractValue operand [1] []
      ]
    , ( LocalReference voidPointer nameValue
      , LocalReference bool nameIsWHNF
      )
    )
  Iridium.TypeAnyThunk ->
    ( []
    , ( operand
      , ConstantOperand $ Int 1 0 -- false
      )
    )
  _ ->
    ( []
    , ( operand
      , ConstantOperand $ Int 1 1 -- true
      )
    )
  where
    operand = toOperand env var
    (nameValue, supply') = freshName supply
    (nameIsWHNF, _) = freshName supply'

-- TODO: Casts from / to int or double
cast :: NameSupply -> Env -> Operand -> Name -> Iridium.PrimitiveType -> Iridium.PrimitiveType -> [Named Instruction]
cast supply env fromOperand toName Iridium.TypeAny Iridium.TypeAny = [toName := AST.BitCast fromOperand taggedThunkPointer []]
cast supply env _ _ (Iridium.TypeGlobalFunction _) _ = error "Cannot cast from GlobalFunction"
cast supply env _ _ _ (Iridium.TypeGlobalFunction _) = error "Cannot cast to GlobalFunction"
cast supply env fromOperand toName fromType Iridium.TypeAny =
  castToVoidPtr
  ++ [ toName := AST.InsertValue
      (ConstantOperand $ Struct Nothing True [Constant.Undef voidPointer, Constant.Int 1 (if fromType == Iridium.TypeAnyThunk then 0 else 1)])
      operandVoid
      [0]
      []
    ]
  where
    (castToVoidPtr, operandVoid)
      | fromType == Iridium.TypeAnyThunk || fromType == Iridium.TypeAnyWHNF = ([], fromOperand)
      | otherwise =
        let
          (name, supply') = freshName supply
        in (cast supply' env fromOperand name fromType Iridium.TypeAnyWHNF, LocalReference voidPointer name)
cast supply env fromOperand toName fromType toType = [toName := AST.BitCast fromOperand toT []]
  where
    toT = compileType env toType
