module Helium.CodeGeneration.LLVM.Env (Env(..), envForModule, EnvMethodInfo(..)) where

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Lvm.Core.Type as Core
import qualified Helium.CodeGeneration.Core.TypeEnvironment as Core
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout(constructorLayout, ConstructorLayout)
import qualified LLVM.AST as AST
import Lvm.Common.IdMap

data Env = Env
  { envTarget :: Target
  , envValueType :: AST.Type
  , envMethod :: Maybe Iridium.Method
  , envConstructors :: IdMap ConstructorLayout
  , envMethodInfo :: IdMap EnvMethodInfo
  -- FFI function name to their external name
  , envFFIInfo :: IdMap String
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
  , envFFIInfo = collectEnvFFIInfo (Iridium.moduleAbstractMethods mod)
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
      ++ fmap (\(Iridium.Declaration name _ _ _ (Iridium.AbstractMethod _ _ _ annotations)) -> (name, methodInfo annotations)) (Iridium.moduleAbstractMethods mod)
    synonyms :: [(Id, Core.Type)]
    synonyms = [(name, tp) | Iridium.Declaration name _ _ _ (Iridium.TypeSynonym _ tp) <- Iridium.moduleTypeSynonyms mod]

data EnvMethodInfo = EnvMethodInfo { envMethodConvention :: !Iridium.CallingConvention, envMethodFakeIO :: !Bool }

methodInfo :: [Iridium.Annotation] -> EnvMethodInfo
methodInfo annotations = EnvMethodInfo (Iridium.callingConvention annotations) (Iridium.AnnotateFakeIO `elem` annotations)

collectEnvFFIInfo :: [Iridium.Declaration Iridium.AbstractMethod] -> IdMap String
collectEnvFFIInfo abstracts = foldl extract emptyMap abstracts
  where
    extract :: IdMap String -> Iridium.Declaration Iridium.AbstractMethod -> IdMap String
    extract ffiMap (Iridium.Declaration name _ _ _ (Iridium.AbstractMethod _ _ ffiInfo _)) =
      case ffiInfo of
        Iridium.FFIInfo (Just foreignName) -> insertMap name foreignName ffiMap
        Iridium.FFIInfo Nothing  -> ffiMap