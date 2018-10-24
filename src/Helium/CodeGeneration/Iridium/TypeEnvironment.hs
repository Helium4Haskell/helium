module Helium.CodeGeneration.Iridium.TypeEnvironment where

import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Data.Maybe(catMaybes)

data TypeEnv = TypeEnv
  { teDataTypes :: !() -- TODO: Do we need this field for a map of data type names to DataType objects?
  , teValues :: !(IdMap ValueDeclaration)
  , teMethod :: !(Maybe (Id, FunctionType))
  }

teReturnType :: TypeEnv -> PrimitiveType
teReturnType (TypeEnv _ _ (Just (_, FunctionType _ retType))) = retType

valueDeclaration :: TypeEnv -> Id -> ValueDeclaration
valueDeclaration env name = findMap name (teValues env)

builtins :: [(Id, ValueDeclaration)]
builtins = -- TODO: This should be replaced by parsing abstract definitions
  [ fn "$primUnsafePerformIO" [TypeAny] TypeAnyWHNF
  , fn "$primPutStrLn" [TypeAny] TypeAnyWHNF
  , fn "$primPatternFailPacked" [TypeAny] TypeAnyWHNF
  , fn "$primConcat" [TypeAny] TypeAnyWHNF
  , fn "$primPackedToString" [TypeAny] TypeAnyWHNF
  , fn "showString" [TypeAny] TypeAnyWHNF
  ]
  where
    fn :: String -> [PrimitiveType] -> PrimitiveType -> (Id, ValueDeclaration)
    fn name args result = (idFromString name, ValueFunction $ FunctionType args result)

data ValueDeclaration
  = ValueConstructor !DataTypeConstructor
  | ValueFunction !FunctionType
  | ValueVariable !PrimitiveType
  deriving (Eq, Ord, Show)

typeOf :: TypeEnv -> Id -> PrimitiveType
typeOf env name = case valueDeclaration env name of
  ValueFunction _ -> TypeFunction
  ValueVariable t -> t

enterFunction :: Id -> FunctionType -> TypeEnv -> TypeEnv
enterFunction name fntype (TypeEnv datas values _) = TypeEnv datas values $ Just (name, fntype)

expandEnvWith :: Local -> TypeEnv -> TypeEnv
expandEnvWith (Local name t) (TypeEnv datas values method) = TypeEnv datas (insertMap name (ValueVariable t) values) method

expandEnvWithLocals :: [Local] -> TypeEnv -> TypeEnv
expandEnvWithLocals args env = foldr (\(Local arg t) -> expandEnvWith $ Local arg t) env args

expandEnvWithLet :: Id -> Expr -> TypeEnv -> TypeEnv
expandEnvWithLet name expr env = expandEnvWith (Local name (typeOfExpr expr)) env

expandEnvWithLetAlloc :: [Bind] -> TypeEnv -> TypeEnv
expandEnvWithLetAlloc thunks env = foldr (\b -> expandEnvWith $ bindLocal b) env thunks

expandEnvWithMatch :: [Maybe Local] -> TypeEnv -> TypeEnv
expandEnvWithMatch locals = expandEnvWithLocals $ catMaybes locals

resolveFunction :: TypeEnv -> Id -> Maybe FunctionType
resolveFunction env name = case lookupMap name (teValues env) of
  Just (ValueFunction fn) -> Just fn
  _ -> Nothing

typeEnvForModule :: Module -> TypeEnv
typeEnvForModule (Module _ dataTypes methods) = TypeEnv () values Nothing
  where
    values = mapFromList $ cons ++ methodDecls
    cons = dataTypes >>= valuesInDataType
    methodDecls = map valueOfMethod methods 

    valuesInDataType :: DataType -> [(Id, ValueDeclaration)]
    valuesInDataType (DataType name cs) = map (\con@(DataTypeConstructor _ conId _) -> (conId, ValueConstructor con)) cs

    valueOfMethod :: Method -> (Id, ValueDeclaration)
    valueOfMethod (Method name args retType _ _) = (name, ValueFunction (FunctionType (map localType args) retType))
