module Helium.CodeGeneration.Iridium.Region.Inference where

import Data.Maybe
import Data.List
import Data.Either
import System.IO

import Lvm.Common.Id
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.AnnotationNormalize
import Helium.CodeGeneration.Iridium.Region.MethodInitialize
import Helium.CodeGeneration.Iridium.Region.MethodRegionArguments
import Helium.CodeGeneration.Iridium.Region.MethodSolveConstraints
import Helium.CodeGeneration.Iridium.Region.MethodTransform
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Utils

regionInference :: NameSupply -> Maybe Handle -> TypeEnvironment -> EffectEnvironment -> BindingGroup Method -> IO (EffectEnvironment, BindingGroup Method)
regionInference supply log typeEnv effectEnv group = do
  let methods = bindingGroupToList group
  debugLog log "### START BINDING GROUP"
  mapM_ (debugLog log . show) methods

  let (_, effectEnv') = foldr assignVar (0, effectEnv) methods

  debugLog log "> Initialize methods"
  let initialize supply (Declaration name _ _ _ method) =
        let (method', state) = methodInitialize typeEnv effectEnv' supply method
        in (method', (name, state))
  let (methods', initializedStateList) = unzip $ mapWithSupply initialize supply methods 
  let initialized = mapFromList initializedStateList
  logStates initialized

  debugLog log "> Assign additional regions to method calls "
  let withRegions = methodsAddRegionArguments effectEnv' initialized
  logStates withRegions

  (effectEnv'', solution) <- methodsSolveConstraints log effectEnv' withRegions
  
  logStates solution

  let group' = mapBindingGroup (methodTransform solution) group

  return (effectEnv'', group)
  where
    assignVar :: Declaration Method -> (Int, EffectEnvironment) -> (Int, EffectEnvironment)
    assignVar (Declaration name _ _ _ (Method t args _ _ _ _)) (idx, env) = (idx', eeInsertGlobal name global env)
      where
        tp = tpFromType [] $ typeNormalize typeEnv t
        sort = typeAnnotationSortArgument effectEnv tp []
        (idx', arg) = sortArgumentToArgument' 0 idx sort
        global = EffectGlobal (length $ rights args) tp $ fmap AVar arg

    logStates :: Show a => IdMap a -> IO ()
    logStates m
      | isJust log = sequence_ $ fmap (\(name, state) -> debugLog log ("%" ++ showId name ":") >> debugLog log (show state)) $ listFromMap m
      | otherwise = return ()
