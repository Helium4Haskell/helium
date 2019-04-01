module Helium.CodeGeneration.LLVM.CompileType (compileType, toOperand, taggedThunkPointer, bool, pointer, trampolineType, voidPointer, splitValueFlag, cast, copy, compileCallingConvention, emptyThunkType) where

import Lvm.Common.Id(Id, freshId, stringFromId, idFromString, NameSupply)
import qualified Lvm.Core.Type as Core
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as Iridium
import LLVM.AST as AST
import LLVM.AST.Constant as Constant
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import qualified LLVM.AST.CallingConvention as CallingConvention

compileType :: Env -> Core.Type -> Type
compileType env tp
  | not $ Core.typeIsStrict tp = taggedThunkPointer
compileType env tp = case skipApp $ skipForallAndStrict $ Iridium.typeNormalizeHead (envTypeEnv env) tp of
  Core.TCon (Core.TConDataType name)
    | name == idFromString "Float" -> FloatingPointType DoubleFP
    | name == idFromString "Int" -> envValueType env
    | name == idFromString "Char" -> envValueType env
    | name == idFromString "$UnsafePtr" -> voidPointer
    | name == idFromString "$Trampoline" -> pointer $ FunctionType voidPointer [voidPointer] False
    | otherwise -> NamedTypeReference $ toNamePrefixed "$data_" name
  _ -> voidPointer

skipApp :: Core.Type -> Core.Type
skipApp (Core.TAp t _) = skipApp t
skipApp t = t

skipForallAndStrict :: Core.Type -> Core.Type
skipForallAndStrict (Core.TForall _ _ t) = skipForallAndStrict t
skipForallAndStrict (Core.TStrict t) = skipForallAndStrict t
skipForallAndStrict tp = tp

compileFunctionType :: Env -> Iridium.FunctionType -> Type
compileFunctionType env (Iridium.FunctionType args returnType) = pointer $ FunctionType (compileType env returnType) argTypes False
  where
    argTypes = [ compileType env tp | Right tp <- args ]

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
toOperand env (Iridium.VarGlobal (Iridium.GlobalFunction name arity tp)) = ConstantOperand $ GlobalReference (compileFunctionType env fntype) (toName name)
  where
    fntype = Iridium.extractFunctionTypeWithArity (envTypeEnv env) arity tp

-- Splits a variable into its value and its tag. Casts to a less-precise type.
splitValueFlag :: Env -> NameSupply -> (Iridium.Variable, Core.Type) -> ([Named Instruction], (Operand, Operand))
splitValueFlag env supply (var, toType)
  | not (Core.typeIsStrict t) =
    ( [ nameValue := AST.ExtractValue operand [0] []
      , nameIsWHNF := AST.ExtractValue operand [1] []
      ]
      -- toType should be non-strict, as it is only allowed to cast to a less-precise type
    , ( LocalReference voidPointer nameValue
      , LocalReference bool nameIsWHNF
      )
    )
  | t == toType' =
    ( []
    , ( operand
      , ConstantOperand $ Int 1 1 -- true
      )
    )
  | otherwise =
    ( cast supply' env operand nameValue t toType'
    , ( LocalReference (compileType env toType') nameValue
      , ConstantOperand $ Int 1 1
      )
    )
  where
    t = Iridium.variableType var
    toType' = Core.typeToStrict toType
    operand = toOperand env var
    (nameValue, supply') = freshName supply
    (nameIsWHNF, _) = freshName supply'

copy :: Env -> Operand -> Name -> Core.Type -> [Named Instruction]
copy env operand name tp =
  [name := Call
    { tailCallKind = Nothing
    , callingConvention = CallingConvention.C
    , returnAttributes = []
    , function = Right $ ConstantOperand $ GlobalReference (pointer $ FunctionType compiledType [compiledType] False) $ mkName "llvm.ssa_copy"
    , arguments = [(operand, [])]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    compiledType = compileType env tp

-- TODO: Casts from / to int or double
cast :: NameSupply -> Env -> Operand -> Name -> Core.Type -> Core.Type -> [Named Instruction]
cast supply env fromOperand toName fromType' toType'
  -- Thunks to thunk - all thunks have the same type in LLVM, so this cast is a no-op
  | not fromStrict && not toStrict
    = copy env fromOperand toName toType
  -- Thunk to WHNF - not allowed in a Cast instruction. This should be done with an Eval statement
  | not fromStrict && toStrict
    = error ("cast: Cannot cast from thunk to WHNF: " ++ show fromOperand ++ ", " ++ show toName ++ show fromType ++ " to " ++ show toType)
  -- Strict to strict - perform bitcast
  | fromStrict && toStrict
    = cast' supply toName
  -- Strict to thunk - perform bitcast from fromType to the strict variant of toType,
  -- then wrap the value in a thunk
  | fromStrict && not toStrict
    = let
        (name, supply') = freshName supply
      in
        cast' supply' name
         ++ [ toName := AST.InsertValue
              (ConstantOperand $ Struct Nothing True [Constant.Undef voidPointer, Constant.Int 1 1])
              (LocalReference (compileType env $ Core.typeToStrict toType) name)
              [0]
              []
            ]
  where
    fromType = Iridium.typeNormalizeHead (envTypeEnv env) fromType'
    toType = Iridium.typeNormalizeHead (envTypeEnv env) toType'
    fromStrict = Core.typeIsStrict fromType
    toStrict = Core.typeIsStrict toType
    fromBase = skipApp $ skipForallAndStrict fromType
    toBase = skipApp $ skipForallAndStrict toType
    -- Checks whether a type is represented in LLVM as a pointer type
    isPointer (Core.TCon (Core.TConDataType name))
      =  name /= idFromString "Int"
      && name /= idFromString "Char"
      && name /= idFromString "Float"
    isPointer _ = True
    fromPointer = isPointer fromBase
    toPointer = isPointer toBase
    cast' supply name
      | fromPointer == toPointer =
        [name := AST.BitCast fromOperand (compileType env toType) []]
      | fromPointer =
        if toBase == Core.TCon (Core.TConDataType $ idFromString "Float") then
          undefined
        else
          [name := AST.PtrToInt fromOperand (envValueType env) []]
      | toPointer =
        if fromBase == Core.TCon (Core.TConDataType $ idFromString "Float") then
          undefined
        else
          [name := AST.IntToPtr fromOperand (compileType env toType) []]

compileCallingConvention :: Iridium.CallingConvention -> CallingConvention.CallingConvention
compileCallingConvention Iridium.CCC = CallingConvention.C
compileCallingConvention Iridium.CCFast = CallingConvention.Fast
compileCallingConvention Iridium.CCPreserveMost = CallingConvention.PreserveMost
