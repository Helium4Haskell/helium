module Helium.CodeGeneration.Iridium.TypeEnvironment where

import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show
import Data.Maybe(catMaybes)

data TypeEnv = TypeEnv
  { teModuleName :: !Id
  , teDataTypes :: !(IdMap [DataTypeConstructor]) -- TODO: Make data types fully qualified
  , teValues :: !(IdMap ValueDeclaration)
  , teMethod :: !(Maybe (Id, FunctionType))
  }

teReturnType :: TypeEnv -> PrimitiveType
teReturnType (TypeEnv _ _ _ (Just (_, FunctionType _ retType))) = retType

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
  -- where
    -- fn :: String -> [PrimitiveType] -> PrimitiveType -> (Id, ValueDeclaration)
    -- fn name args result = (idFromString name, ValueFunction $ FunctionType args result)

data ValueDeclaration
  = ValueConstructor !DataTypeConstructor
  | ValueFunction !Id !FunctionType !CallingConvention
  | ValueVariable !PrimitiveType
  deriving (Eq, Ord, Show)

typeOf :: TypeEnv -> Id -> PrimitiveType
typeOf env name = case valueDeclaration env name of
  ValueFunction _ (FunctionType [] t) _ -> TypeAnyThunk
  ValueFunction _ fntype _ -> TypeGlobalFunction fntype
  ValueVariable t -> t

enterFunction :: Id -> FunctionType -> TypeEnv -> TypeEnv
enterFunction name fntype (TypeEnv moduleName datas values _) = TypeEnv moduleName datas values $ Just (name, fntype)

expandEnvWith :: Local -> TypeEnv -> TypeEnv
expandEnvWith (Local name t) (TypeEnv moduleName datas values method) = TypeEnv moduleName datas (insertMap name (ValueVariable t) values) method

expandEnvWithLocals :: [Local] -> TypeEnv -> TypeEnv
expandEnvWithLocals args env = foldr (\(Local arg t) -> expandEnvWith $ Local arg t) env args

expandEnvWithLet :: Id -> Expr -> TypeEnv -> TypeEnv
expandEnvWithLet name expr env = expandEnvWith (Local name (typeOfExpr expr)) env

expandEnvWithLetAlloc :: [Bind] -> TypeEnv -> TypeEnv
expandEnvWithLetAlloc thunks env = foldr (\b -> expandEnvWith $ bindLocal b) env thunks

expandEnvWithMatch :: [Maybe Local] -> TypeEnv -> TypeEnv
expandEnvWithMatch locals = expandEnvWithLocals $ catMaybes locals

resolveFunction :: TypeEnv -> Id -> Maybe (Id, FunctionType)
resolveFunction env name = case lookupMap name (teValues env) of
  Just (ValueFunction qualifiedName fn _) -> Just (qualifiedName, fn)
  _ -> Nothing

valueOfMethod :: Id -> Declaration Method -> (Id, ValueDeclaration)
valueOfMethod name (Declaration qualifiedName _ _ _ (Method args retType annotations _ _)) = (name, ValueFunction qualifiedName (FunctionType (map localType args) retType) $ callingConvention annotations)

valueOfAbstract :: Id -> Declaration AbstractMethod -> (Id, ValueDeclaration)
valueOfAbstract name (Declaration qualifiedName _ _ _ (AbstractMethod fntype annotations)) = (name, ValueFunction qualifiedName fntype $ callingConvention annotations)
