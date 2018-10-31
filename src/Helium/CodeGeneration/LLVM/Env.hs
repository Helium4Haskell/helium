module Helium.CodeGeneration.LLVM.Env where

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout(constructorLayout, ConstructorLayout)
import qualified LLVM.AST as AST
import Lvm.Common.IdMap

data Env = Env
  { envTarget :: Target
  , envValueType :: AST.Type
  , envMethod :: Maybe Iridium.Method
  , envConstructors :: IdMap ConstructorLayout
  }

envForModule :: Target -> Iridium.Module -> Env
envForModule target mod = Env
  { envTarget = target
  , envValueType = AST.IntegerType $ fromIntegral $ targetWordSize target
  , envMethod = Nothing
  , envConstructors = mapFromList constructors
  }
  where
    typeEnv = TypeEnv.typeEnvForModule mod
    constructors = Iridium.moduleDataTypes mod >>=
      (\dataTypeDecl@(Iridium.Declaration name _ _ dataType) ->
        zipWith
          (\con@(Iridium.DataTypeConstructor _ conName _) index ->
            (conName, constructorLayout typeEnv target dataType index con))
          (Iridium.getConstructors dataTypeDecl)
          [0..]
      )
