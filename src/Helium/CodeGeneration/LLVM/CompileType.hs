module Helium.CodeGeneration.LLVM.CompileType (compileType, toOperand, taggedThunkPointer, bool, pointer, trampolineType, voidPointer, splitValueFlag, cast, compileCallingConvention, emptyThunkType) where

import Lvm.Common.Id(Id, freshId, stringFromId, NameSupply)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST as AST
import LLVM.AST.Constant as Constant
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import qualified LLVM.AST.CallingConvention as CallingConvention

compileType :: Env -> Iridium.PrimitiveType -> Type
compileType env Iridium.TypeAny = taggedThunkPointer
compileType env Iridium.TypeAnyThunk = voidPointer
compileType env Iridium.TypeAnyWHNF = voidPointer
compileType env Iridium.TypeInt = envValueType env
compileType env (Iridium.TypeFloat Iridium.Float32) = FloatingPointType FloatFP
compileType env (Iridium.TypeFloat Iridium.Float64) = FloatingPointType DoubleFP
compileType env Iridium.TypeRealWorld = envValueType env
compileType env (Iridium.TypeDataType dataName) = NamedTypeReference $ toNamePrefixed "$data_" dataName
compileType env (Iridium.TypeTuple _) = voidPointer
compileType env Iridium.TypeFunction = voidPointer
compileType env (Iridium.TypeGlobalFunction fntype) = compileFunctionType env fntype
compileType env Iridium.TypeUnsafePtr = voidPointer

compileFunctionType :: Env -> Iridium.FunctionType -> Type
compileFunctionType env (Iridium.FunctionType args returnType) = pointer $ FunctionType (compileType env returnType) (map (compileType env) args) False

trampolineType :: Type
trampolineType = pointer $ FunctionType voidPointer [voidPointer] False

emptyThunkType :: Type
emptyThunkType = StructureType False [IntegerType 64, IntegerType 64, trampolineType]

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
toOperand env (Iridium.VarGlobal (Iridium.GlobalVariable name t)) = ConstantOperand $ Constant.BitCast (GlobalReference (pointer emptyThunkType) (toNamePrefixed "thunk$" name)) (compileType env t)
toOperand env (Iridium.VarGlobal (Iridium.GlobalFunction name fntype)) = ConstantOperand $ GlobalReference (compileFunctionType env fntype) (toName name)

-- Splits a variable into its value and its tag. Casts to a less-precise type.
splitValueFlag :: Env -> NameSupply -> (Iridium.Variable, Iridium.PrimitiveType) -> ([Named Instruction], (Operand, Operand))
splitValueFlag env supply (var, toType) = case t of
  Iridium.TypeAny ->
    ( [ nameValue := AST.ExtractValue operand [0] []
      , nameIsWHNF := AST.ExtractValue operand [1] []
      ]
      -- toType should be TypeAny, as it is only allowed to cast to a less-precise type
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
  _
    | t == toType' ->
      ( []
      , ( operand
        , ConstantOperand $ Int 1 1 -- true
        )
      )
    | otherwise ->
      ( cast supply' env operand nameValue t toType'
      , ( LocalReference (compileType env toType') nameValue
        , ConstantOperand $ Int 1 1
        )
      )
  where
    t = Iridium.variableType var
    -- Remove flag from type
    toType' = if toType == Iridium.TypeAny then Iridium.TypeAnyWHNF else toType
    operand = toOperand env var
    (nameValue, supply') = freshName supply
    (nameIsWHNF, _) = freshName supply'

-- TODO: Casts from / to int or double
cast :: NameSupply -> Env -> Operand -> Name -> Iridium.PrimitiveType -> Iridium.PrimitiveType -> [Named Instruction]
cast supply env fromOperand toName fromType toType
  | fromType == toType = [toName := AST.Select (ConstantOperand $ Constant.Int 1 1) fromOperand (ConstantOperand $ Constant.Undef toT) []]
  where
    toT = compileType env toType
cast supply env _ name (Iridium.TypeGlobalFunction _) _ = error $ "Cannot cast from GlobalFunction (" ++ show name ++ ")"
cast supply env _ name _ (Iridium.TypeGlobalFunction _) = error $ "Cannot cast to GlobalFunction (" ++ show name ++ ")"
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
cast supply env _ toName fromType toType
  | fromType == Iridium.TypeRealWorld || toType == Iridium.TypeRealWorld = [toName := AST.Select (ConstantOperand $ Constant.Int 1 1) undef undef []]
  where
    undef = ConstantOperand $ Constant.Undef $ compileType env toType
cast supply env fromOperand toName (Iridium.TypeFloat Iridium.Float64) toType = 
  [nameInt := AST.BitCast fromOperand (envValueType env) []]
  ++ cast supply' env (LocalReference (envValueType env) nameInt) toName Iridium.TypeInt toType
  where
    (nameInt, supply') = freshName supply
cast supply env fromOperand toName fromType (Iridium.TypeFloat Iridium.Float64) =
  cast supply' env fromOperand nameInt fromType Iridium.TypeInt
  ++ [toName := AST.BitCast (LocalReference (envValueType env) nameInt) (compileType env ((Iridium.TypeFloat Iridium.Float64))) []]
  where
    (nameInt, supply') = freshName supply
cast supply env fromOperand toName fromType Iridium.TypeInt = [toName := AST.PtrToInt fromOperand (envValueType env) []]
cast supply env fromOperand toName Iridium.TypeInt toType = [toName := AST.IntToPtr fromOperand (compileType env toType) []]
cast supply env fromOperand toName fromType toType = [toName := AST.BitCast fromOperand toT []]
  where
    toT = compileType env toType

compileCallingConvention :: Iridium.CallingConvention -> CallingConvention.CallingConvention
compileCallingConvention Iridium.CCC = CallingConvention.C
compileCallingConvention Iridium.CCFast = CallingConvention.Fast
compileCallingConvention Iridium.CCPreserveMost = CallingConvention.PreserveMost
