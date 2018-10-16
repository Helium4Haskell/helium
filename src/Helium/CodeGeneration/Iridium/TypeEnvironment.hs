module Helium.CodeGeneration.Iridium.TypeEnvironment where

import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

data TypeEnv = TypeEnv
  { teDataTypes :: () -- TODO: Do we need this field for a map of data type names to DataType objects?
  , teValues :: IdMap ValueDeclaration
  }

valueDeclaration :: TypeEnv -> Id -> ValueDeclaration
valueDeclaration env name = findMap name (teValues env)

builtins :: [(Id, ValueDeclaration)]
builtins =
  [ fn "$primUnsafePerformIO" [TypeAny] TypeAnyWHNF
  , fn "$primPutStrLn" [TypeAny] TypeAnyWHNF
  , fn "$primPatternFailPacked" [TypeAny] TypeAnyWHNF
  , fn "$primConcat" [TypeAny] TypeAnyWHNF
  , fn "$primPackedToString" [TypeAny] TypeAnyWHNF
  ]
  where
    fn :: String -> [PrimitiveType] -> PrimitiveType -> (Id, ValueDeclaration)
    fn name args result = (idFromString name, ValueFunction $ FunctionType args result)

data ValueDeclaration
  = ValueConstructor Id DataTypeConstructor
  | ValueFunction FunctionType
  | ValueVariable PrimitiveType
  deriving (Eq, Ord, Show)

typeOf :: TypeEnv -> Id -> PrimitiveType
typeOf env name = case valueDeclaration env name of
  ValueConstructor dataName (DataTypeConstructor _ []) -> TypeDataType dataName
  ValueConstructor _ _ -> error "typeOf: Unsaturated constructor cannot be used as a value."
  ValueFunction _ -> TypeFunction
  ValueVariable t -> t

typeOfExpr :: TypeEnv -> Expr -> PrimitiveType
typeOfExpr env (Literal (LitDouble _)) = TypeDouble
typeOfExpr env (Literal _) = TypeInt
typeOfExpr env (Call to _) = case findMap to (teValues env) of
  ValueFunction (FunctionType _ ret) -> ret
  _ -> error "typeOfExpr: Illegal target of Call expression. Expected a function declaration."
typeOfExpr env (Eval _) = TypeAnyWHNF
typeOfExpr env (Alloc con args) = case findMap con (teValues env) of
  ValueConstructor dataName _ -> TypeDataType dataName
  _ -> error "typeOfExpr: Illegal target of Alloc expression. Expected a constructor."
typeOfExpr env (Var (Variable _ t)) = t
typeOfExpr env (Cast _ t) = t

expandEnvWith :: Id -> PrimitiveType -> TypeEnv -> TypeEnv
expandEnvWith name t (TypeEnv datas values) = TypeEnv datas $ insertMap name (ValueVariable t) values

expandEnvWithArguments :: [Variable] -> TypeEnv -> TypeEnv
expandEnvWithArguments args env = foldr (\(Variable arg t) -> expandEnvWith arg t) env args

expandEnvWithLet :: Id -> Expr -> TypeEnv -> TypeEnv
expandEnvWithLet name expr env = expandEnvWith name (typeOfExpr env expr) env

expandEnvWithLetThunk :: [BindThunk] -> TypeEnv -> TypeEnv
expandEnvWithLetThunk thunks (TypeEnv datas values) = TypeEnv datas $ foldr (\(BindThunk var _ _) -> insertMap var (ValueVariable TypeAnyThunk)) values thunks

declarationsInMatch :: TypeEnv -> Id -> [Id] -> [(Id, ValueDeclaration)]
declarationsInMatch env con args = case findMap con (teValues env) of
  ValueConstructor _ (DataTypeConstructor _ fields) -> zip args $ map ValueVariable fields
  _ -> error "declarationsInMatch: Illegal constructor name in a pattern. Expected a constructor."

expandEnvWithMatch :: Id -> [Id] -> TypeEnv -> TypeEnv
expandEnvWithMatch con args env@(TypeEnv datas values) = TypeEnv datas $ foldr (\(var, decl) -> insertMap var decl) values $ declarationsInMatch env con args

argumentsOf :: TypeEnv -> Id -> Maybe [PrimitiveType]
argumentsOf env name = case lookupMap name (teValues env) of
  Just (ValueFunction (FunctionType args _)) -> Just args
  _ -> Nothing

typeEnvForModule :: Module -> TypeEnv
typeEnvForModule (Module _ dataTypes methods) = TypeEnv () values
  where
    values = mapFromList $ cons ++ methodDecls
    cons = dataTypes >>= valuesInDataType
    methodDecls = map valueOfMethod methods 

    valuesInDataType :: DataType -> [(Id, ValueDeclaration)]
    valuesInDataType (DataType name cs) = map (\con@(DataTypeConstructor conId _) -> (conId, ValueConstructor name con)) cs

    valueOfMethod :: Method -> (Id, ValueDeclaration)
    valueOfMethod (Method name args retType _ _) = (name, ValueFunction (FunctionType (map variableType args) retType))
