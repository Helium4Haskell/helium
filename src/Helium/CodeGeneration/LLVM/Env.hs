module Helium.CodeGeneration.LLVM.Env where

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout(constructorLayout, ConstructorLayout)
import qualified LLVM.AST as AST
import Lvm.Common.IdMap

expand :: Env -> (TypeEnv.TypeEnv -> TypeEnv.TypeEnv) -> Env
expand env fn = env{ envTypeEnv = fn $ envTypeEnv env }

data Env = Env
  { envTarget :: Target
  , envValueType :: AST.Type
  , envTypeEnv :: TypeEnv.TypeEnv
  , envMethod :: Maybe Iridium.Method
  , envConstructors :: IdMap ConstructorLayout
  }

envForModule :: Target -> Iridium.Module -> Env
envForModule target mod = Env
  { envTarget = target
  , envValueType = AST.IntegerType $ fromIntegral $ targetPointerSize target
  , envTypeEnv = typeEnv
  , envMethod = Nothing
  , envConstructors = mapFromList constructors
  }
  where
    typeEnv = TypeEnv.typeEnvForModule mod
    constructors = Iridium.moduleDataTypes mod >>=
      (\dataType@(Iridium.DataType name cons) ->
        zipWith
          (\con@(Iridium.DataTypeConstructor _ conName _) index ->
            (conName, constructorLayout typeEnv target dataType index con))
          cons
          [0..]
      )
