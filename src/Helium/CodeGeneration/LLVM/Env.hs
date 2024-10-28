module Helium.CodeGeneration.LLVM.Env (Env(..), envForModule, EnvMethodInfo(..)) where

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.Lvm.Core.Type as Core
import qualified Helium.CodeGeneration.Core.TypeEnvironment as Core
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout(constructorLayout, ConstructorLayout)
import qualified LLVM.AST as AST
import Helium.Lvm.Common.IdMap

data Env = Env
  { envTarget :: Target
  , envValueType :: AST.Type
  , envMethod :: Maybe Iridium.Method
  , envConstructors :: IdMap ConstructorLayout
  , envMethodInfo :: IdMap EnvMethodInfo
  -- Environment is only used for type synonyms
  , envTypeEnv :: Core.TypeEnvironment
  }

envForModule :: Target -> Iridium.Module -> Env
envForModule target mod = Env
  { envTarget = target
  , envValueType = AST.IntegerType $ fromIntegral $ targetWordSize target
  , envMethod = Nothing
  , envConstructors = mapFromList constructors
  , envMethodInfo = mapFromList methods
  -- Environment is only used for type synonyms
  , envTypeEnv = Core.TypeEnvironment (mapFromList synonyms) emptyMap emptyMap
  }
  where
    constructors = Iridium.moduleDataTypes mod >>=
      (\dataTypeDecl@(Iridium.Declaration name _ _ _ dataType) ->
        zipWith
          (\con@(Iridium.DataTypeConstructor conName _) index ->
            (conName, constructorLayout target dataType index con))
          (Iridium.getConstructors dataTypeDecl)
          [0..]
      )
    methods :: [(Id, EnvMethodInfo)]
    methods = fmap (\(Iridium.Declaration name _ _ _ (Iridium.Method _ _ _ annotations _ _)) -> (name, methodInfo annotations)) (Iridium.moduleMethods mod)
      ++ fmap (\(Iridium.Declaration name _ _ _ (Iridium.AbstractMethod _ _ annotations)) -> (name, methodInfo annotations)) (Iridium.moduleAbstractMethods mod)
    synonyms :: [(Id, Core.Type)]
    synonyms = [(name, tp) | Iridium.Declaration name _ _ _ (Iridium.TypeSynonym _ tp) <- Iridium.moduleTypeSynonyms mod]

data EnvMethodInfo = EnvMethodInfo { envMethodConvention :: !Iridium.CallingConvention, envMethodImplicitIO :: !Bool }

methodInfo :: [Iridium.Annotation] -> EnvMethodInfo
methodInfo annotations = EnvMethodInfo (Iridium.callingConvention annotations) (Iridium.AnnotateImplicitIO `elem` annotations)
