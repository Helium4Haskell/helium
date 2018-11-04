module Helium.CodeGeneration.Iridium.TypeEnvironment where

import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show
import Data.Maybe(catMaybes)

data TypeEnv = TypeEnv
  { teDataTypes :: !(IdMap [DataTypeConstructor])
  , teValues :: !(IdMap ValueDeclaration)
  , teMethod :: !(Maybe (Id, FunctionType))
  }

teReturnType :: TypeEnv -> PrimitiveType
teReturnType (TypeEnv _ _ (Just (_, FunctionType _ retType))) = retType

valueDeclaration :: TypeEnv -> Id -> ValueDeclaration
valueDeclaration env name = findMap name (teValues env)

builtins :: [(Id, ValueDeclaration)]
builtins = -- TODO: This should be replaced by parsing abstract definitions
  [ {- fn "$primUnsafePerformIO" [TypeAny] TypeAnyWHNF
  , fn "$primPutStrLn" [TypeAny] TypeAnyWHNF
  , fn "$primPatternFailPacked" [TypeDataType $ idFromString "[]"] TypeAnyWHNF
  , fn "$primConcat" [TypeAny] TypeAnyWHNF
  , fn "$primPackedToString" [TypeDataType $ idFromString "[]"] TypeAnyWHNF
  , fn "showString" [TypeAny] TypeAnyWHNF
  -} ]
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
  ValueFunction fntype -> TypeGlobalFunction fntype
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
typeEnvForModule (Module _ _ _ dataTypes abstracts methods) = TypeEnv dataTypeMap values Nothing
  where
    values = mapFromList $ cons ++ methodDecls ++ abstractDecls
    dataTypeMap = mapFromList $ map (\d@(Declaration name _ _ _) -> (name, getConstructors d)) dataTypes
    cons = dataTypes >>= valuesInDataType
    methodDecls = map valueOfMethod methods 
    abstractDecls = map valueOfAbstract abstracts

    valuesInDataType :: Declaration DataType -> [(Id, ValueDeclaration)]
    valuesInDataType (Declaration name _ _ (DataType cs)) = map (\(Declaration conId _ _ (DataTypeConstructorDeclaration args)) -> (conId, ValueConstructor $ DataTypeConstructor name conId args)) cs

    valueOfMethod :: Declaration Method -> (Id, ValueDeclaration)
    valueOfMethod (Declaration name _ _ (Method args retType _ _)) = (name, ValueFunction (FunctionType (map localType args) retType))

    valueOfAbstract :: Declaration AbstractMethod -> (Id, ValueDeclaration)
    valueOfAbstract (Declaration name _ _ (AbstractMethod fntype)) = (name, ValueFunction fntype)
