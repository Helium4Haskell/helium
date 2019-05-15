module Helium.CodeGeneration.Iridium.Region.Inference where

import Data.Maybe
import System.IO

import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Show
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.Method
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Utils

regionInference :: Maybe Handle -> TypeEnvironment -> EffectEnvironment -> BindingGroup Method -> IO (EffectEnvironment, BindingGroup Method)
regionInference log typeEnv effectEnv group = do
  let methods = bindingGroupToList group
  debugLog log "### START BINDING GROUP"
  mapM_ (debugLog log . show) methods

  let initialized = mapFromList $ map (\(Declaration name _ _ _ method) -> (name, methodInitialize typeEnv effectEnv method)) methods
  logStates initialized 

  return (effectEnv, group)
  where
    logStates :: IdMap MethodState -> IO ()
    logStates m
      | isJust log = sequence_ $ fmap (\(name, state) -> debugLog log ("%" ++ showId name ":") >> debugLog log (show state)) $ listFromMap m
      | otherwise = return ()
