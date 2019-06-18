-- Assigns additional region arguments to a function for function calls.

module Helium.CodeGeneration.Iridium.Region.MethodRegionArguments (methodsAddRegionArguments) where

import Data.Maybe
import Data.List

import Lvm.Common.Id
import Lvm.Common.IdMap

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.MethodInitialize

data MethodCallRegions
  = MethodCallRegions
    { mcrIdentifier :: !Id
    , mcrTarget :: !Id
    -- Just for non-recursive calls, Nothing for recursive calls
    , mcrRegionArguments :: !(Maybe Int)
    }

methodsAddRegionArguments :: EffectEnvironment -> IdMap MethodState -> IdMap MethodState
methodsAddRegionArguments env states = mapMapWithId (methodAddRegionArguments env methods) states
  where
    methods = mapMap (methodRegions env) states

methodAddRegionArguments :: EffectEnvironment -> IdMap MethodRegions -> Id -> MethodState -> MethodState
methodAddRegionArguments env methods name state = assignAdditionalRegionVariables count (applyCallRegions methods name methodRegions) state
  where
    methodRegionCount = countCallRegions methods [] name
    methodRegions = map (variableFromIndices (msAdditionalArgumentScope state)) [0 .. methodRegionCount - 1]
    count :: Constraint -> Int
    count CCall{cCallTarget = Left target} = countCallRegions methods [name] target
    count _ = 0

data MethodRegions = MethodRegions { mrRegionCount :: !Int, mrCallRegions :: ![MethodCallRegions] }
type MethodRegionsMap = IdMap MethodRegions

methodRegions :: EffectEnvironment -> MethodState -> MethodRegions
methodRegions env method = MethodRegions arguments mcrs
  where
    arguments = msRegionCount method
    mcrs = mapMaybe (constraintRegions env) $ msConstraints method

constraintRegions :: EffectEnvironment -> Constraint -> Maybe MethodCallRegions
constraintRegions env (CCall lhs _ _ _ (Left target) _ _ _ _) = Just $ MethodCallRegions lhs target arguments
  where
    EffectGlobal _ _ annotation = eeLookupGlobal env target
    arguments = case annotation of
      ArgumentList [] -> Just 0
      ArgumentList (ArgumentValue (ALam _ (SortArgumentList args) _) : _) -> Just $ length args
      _ -> Nothing
constraintRegions _ _ = Nothing

countCallRegions :: MethodRegionsMap -> [Id] -> Id -> Int
countCallRegions methods = count
  where
    count :: [Id] -> Id -> Int
    count stack name
      | name `elem` stack = 0 -- Recursive
      | otherwise = count + sum (map (countCall (name : stack)) calls)
      where
        MethodRegions count calls = findMap name methods

    countCall :: [Id] -> MethodCallRegions -> Int
    countCall _ (MethodCallRegions _ _ (Just c)) = c
    countCall stack (MethodCallRegions _ target _) = count stack target

applyCallRegions :: MethodRegionsMap -> Id -> [RegionVar] -> Constraint -> [RegionVar] -> [RegionVar]
applyCallRegions methods root recursive CCall{ cCallTarget = Left name } allRegions = snd $ apply [] allRegions name
  where
    apply :: [Id] -> [RegionVar] -> Id -> ([RegionVar], [RegionVar])
    apply stack freshRegions name
      | root == name = (freshRegions, recursive)
      | name `elem` stack = (freshRegions, [])
      | otherwise = (freshRegions'', regions ++ concat regionsCall)
      where
        (regions, freshRegions') = splitAt count freshRegions
        (freshRegions'', regionsCall) = mapAccumL (applyCall stack) freshRegions' calls
        MethodRegions count calls = findMap name methods

    applyCall :: [Id] -> [RegionVar] -> MethodCallRegions -> ([RegionVar], [RegionVar])
    applyCall stack freshRegions (MethodCallRegions _ _ (Just count)) = (freshRegions', regions)
      where
        (regions, freshRegions') = splitAt count freshRegions
    applyCall stack freshRegions (MethodCallRegions _ target _) = apply stack freshRegions target
applyCallRegions _ _ _ _ _ = []

