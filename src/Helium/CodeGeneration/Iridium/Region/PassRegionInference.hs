module Helium.CodeGeneration.Iridium.Region.PassRegionInference where

import System.IO
import Lvm.Common.Id
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.DataType
import Helium.CodeGeneration.Iridium.Region.Method
import Helium.CodeGeneration.Iridium.Region.Inference

import Debug.Trace

passRegionInference :: NameSupply -> Module -> Module
passRegionInference supply mod@(Module _ _ _ _ _ _ methods) = traceShow effectEnvDataTypes mod
  where
    groups = methodBindingGroups methods
    -- TODO: Handle AbstractMethods
    typeEnv = envWithSynonyms mod
    effectEnvDataTypes = effectDataTypes typeEnv mod

type AccumState = (NameSupply, EffectEnvironment)
handleBindingGroups :: Maybe Handle -> TypeEnvironment -> AccumState -> [BindingGroup Method] -> IO (AccumState, [BindingGroup Method])
handleBindingGroups _ _ accum [] = accum `seq` return (accum, [])
handleBindingGroups log typeEnv (supply, effectEnv) (group : groups) = do
  let (supply1, supply2) = splitNameSupply supply
  (effectEnv', group') <- regionInference log typeEnv effectEnv group
  (accumState, groups') <- handleBindingGroups log typeEnv (supply2, effectEnv') groups
  return (accumState, group' : groups')
