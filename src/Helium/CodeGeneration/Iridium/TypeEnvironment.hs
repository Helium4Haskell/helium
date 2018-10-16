module Helium.CodeGeneration.Iridium.TypeEnvironment where

import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Data.Maybe(catMaybes)

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
  = ValueConstructor DataTypeConstructor
  | ValueFunction FunctionType
  | ValueVariable PrimitiveType
  deriving (Eq, Ord, Show)

typeOf :: TypeEnv -> Id -> PrimitiveType
typeOf env name = case valueDeclaration env name of
  ValueFunction _ -> TypeFunction
  ValueVariable t -> t

expandEnvWith :: Id -> PrimitiveType -> TypeEnv -> TypeEnv
expandEnvWith name t (TypeEnv datas values) = TypeEnv datas $ insertMap name (ValueVariable t) values

expandEnvWithLocals :: [Local] -> TypeEnv -> TypeEnv
expandEnvWithLocals args env = foldr (\(Local arg t) -> expandEnvWith arg t) env args

expandEnvWithLet :: Id -> Expr -> TypeEnv -> TypeEnv
expandEnvWithLet name expr env = expandEnvWith name (typeOfExpr expr) env

expandEnvWithLetThunk :: [BindThunk] -> TypeEnv -> TypeEnv
expandEnvWithLetThunk thunks (TypeEnv datas values) = TypeEnv datas $ foldr (\(BindThunk var _ _) -> insertMap var (ValueVariable TypeAnyThunk)) values thunks

expandEnvWithMatch :: [Maybe Local] -> TypeEnv -> TypeEnv
expandEnvWithMatch locals = expandEnvWithLocals $ catMaybes locals

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
    valuesInDataType (DataType name cs) = map (\con@(DataTypeConstructor _ conId _) -> (conId, ValueConstructor con)) cs

    valueOfMethod :: Method -> (Id, ValueDeclaration)
    valueOfMethod (Method name args retType _ _) = (name, ValueFunction (FunctionType (map localType args) retType))
