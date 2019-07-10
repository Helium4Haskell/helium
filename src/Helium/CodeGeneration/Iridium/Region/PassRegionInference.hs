module Helium.CodeGeneration.Iridium.Region.PassRegionInference where

import System.IO
import Data.Maybe
import Lvm.Common.Id
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.DataType
import Helium.CodeGeneration.Iridium.Region.Inference
import Helium.CodeGeneration.Iridium.Region.Utils

import Debug.Trace

passRegionInference :: Maybe FilePath  -> NameSupply -> Module -> IO Module
passRegionInference (Just path) supply mod =
  withFile path WriteMode (\handle -> passRegionInference' (Just handle) supply mod)
passRegionInference Nothing supply mod = passRegionInference' Nothing supply mod

passRegionInference' :: Maybe Handle -> NameSupply -> Module -> IO Module
passRegionInference' log supply mod@(Module _ _ _ _ _ abstracts methods) = do
  let typeEnv = envWithSynonyms mod
  let effectEnvDataTypes = effectDataTypes typeEnv mod
  let effectEnvAbstracts = foldr (insertAbstractMethod typeEnv) effectEnvDataTypes abstracts

  let groups = methodBindingGroups methods

  debugLog log (show effectEnvAbstracts)

  ((_, finalEnv), groups') <- handleBindingGroups log typeEnv (supply, effectEnvAbstracts) groups

  return mod{moduleMethods = groups' >>= bindingGroupToList }

insertAbstractMethod :: TypeEnvironment -> Declaration AbstractMethod -> EffectEnvironment -> EffectEnvironment
insertAbstractMethod typeEnv (Declaration name _ _ _ (AbstractMethod arity t annotations)) effectEnv = eeInsertGlobal name global effectEnv
  where
    tp = tpFromType [] $ typeNormalize typeEnv t
    sort = typeAnnotationSortArgument effectEnv tp []
    arg = sortArgumentToArgument 0 sort :: Argument AnnotationVar
    bottom = trace ("Warning: abstract method " ++ show name ++ " has no region annotation") $ fmap (const ABottom) arg
    global = EffectGlobal arity tp $ fmap (const ABottom) $ fromMaybe bottom $ findRegionMethodAnnotation annotations

findRegionMethodAnnotation :: [MethodAnnotation] -> Maybe (Argument Annotation)
findRegionMethodAnnotation [] = Nothing
findRegionMethodAnnotation (MethodAnnotateRegion args : _) = Just args
findRegionMethodAnnotation (_ : annotations) = findRegionMethodAnnotation annotations

type AccumState = (NameSupply, EffectEnvironment)
handleBindingGroups :: Maybe Handle -> TypeEnvironment -> AccumState -> [BindingGroup Method] -> IO (AccumState, [BindingGroup Method])
handleBindingGroups _ _ accum [] = accum `seq` return (accum, [])
handleBindingGroups log typeEnv (supply, effectEnv) (group : groups) = do
  let (supply1, supply2) = splitNameSupply supply
  (effectEnv', group') <- regionInference supply1 log typeEnv effectEnv group
  (accumState, groups') <- handleBindingGroups log typeEnv (supply2, effectEnv') groups
  return (accumState, group' : groups')
