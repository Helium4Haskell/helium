-- Program transformation after region inference.
-- Adds region arguments and annotations to methods
-- and annotates binds and calls with regions.

module Helium.CodeGeneration.Iridium.Region.Transform (transform) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Generate

import Data.Maybe
import Data.Either

transform :: MethodEnv -> (RegionVar -> RegionVar) -> Annotation -> Method -> Method
transform env substitute annotation (Method tp _ args returnType _ methodAnnotations entry blocks)
  = Method tp additionalRegions args returnType returnRegions methodAnnotations (transformBlock regions True entry) (transformBlock regions False <$> blocks)
  where
    substitute' :: RegionVar -> RegionVar
    substitute' var = case substitute var of
      RegionBottom -> var -- Internal region
      var' -> var'

    regions = Regions
      (\name -> substitutes $ snd $ findMap name $ methodEnvVars env)
      (\name -> map substitute' $ fromMaybe [] $ lookupMap name $ methodEnvAdditionalFor env)
      (filter (\var -> substitute var == RegionBottom) $ flattenRegionVars $ methodEnvAdditionalRegionVars env)

    substitutes :: RegionVars -> RegionVars
    substitutes = mapRegionVars substitute'

    additionalRegions
      = RegionVarsTuple
      $ map RegionVarsSingle
      $ filter (\var -> substitute var == var)
      $ flattenRegionVars
      $ methodEnvAdditionalRegionVars env

    returnRegions = methodEnvReturnRegions env

data Regions = Regions
  { localRegions :: Id -> RegionVars
  , additionalRegionsFor :: Id -> [RegionVar]
  , internalRegions :: [RegionVar]
  }

transformBlock :: Regions -> Bool -> Block -> Block
transformBlock regions isEntry (Block name instr) = Block name $ instrAlloc $ transformInstruction regions instr
  where
    instrAlloc
      | isEntry = id -- TODO: Allocate internal regions
      | otherwise = id

transformInstruction :: Regions -> Instruction -> Instruction
transformInstruction regions instruction = case instruction of
  Let name expr next -> Let name (transformExpr regions name expr) (go next)
  LetAlloc binds next -> LetAlloc (transformBind regions <$> binds) (go next)
  Jump block -> Jump block
  Match var target instantiation fields next -> Match var target instantiation fields $ go next
  Case var c -> Case var c
  Return var -> id $ Return var -- TODO: deallocate regions
  Unreachable var -> Unreachable var
  where
    go = transformInstruction regions

transformExpr :: Regions -> Id -> Expr -> Expr
transformExpr regions lhs expr = case expr of
  Call fn _ args _ -> Call fn (RegionVarsTuple $ map RegionVarsSingle $ additionalRegionsFor regions lhs) args (localRegions regions lhs)
  _ -> expr

transformBind :: Regions -> Bind -> Bind
transformBind regions (Bind lhs target args _) = Bind lhs target' args $ head $ flattenRegionVars regionVars
  where
    target' = transformBindTarget (additionalRegionsFor regions lhs) regionVars target (length $ rights args)
    regionVars = localRegions regions lhs

transformBindTarget :: [RegionVar] -> RegionVars -> BindTarget -> Int -> BindTarget
transformBindTarget additionalRegions regionVars (BindTargetThunk var _) _
  = BindTargetThunk var
  $ BindThunkRegions (RegionVarsTuple $ map RegionVarsSingle additionalRegions) -- Regions for intermediate thunks, in case of an oversatured thunk.
  $ regionsAsStrict regionVars
transformBindTarget additionalRegions regionVars (BindTargetFunction fn _ _) valueArguments
  = BindTargetFunction fn (RegionVarsTuple $ map RegionVarsSingle callAdditionalRegions)
  $ BindThunkRegions (RegionVarsTuple $ map RegionVarsSingle intermediateRegions)
  $ regionsAsStrict regionVars
  where
    intermediateRegionCount = max 0 (valueArguments - 1)
    callAdditionalRegionCount = length additionalRegions - intermediateRegionCount
    callAdditionalRegions = take callAdditionalRegionCount additionalRegions
    intermediateRegions = drop callAdditionalRegionCount additionalRegions
transformBindTarget _ _ target _ = target

regionsAsStrict :: RegionVars -> RegionVars
regionsAsStrict (RegionVarsTuple [_, r1, r2]) = RegionVarsTuple [r1, r2]
regionsAsStrict r = r
