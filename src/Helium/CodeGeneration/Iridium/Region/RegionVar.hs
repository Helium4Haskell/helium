{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Helium.CodeGeneration.Iridium.Region.RegionVar
  ( RegionVar(..), pattern RegionGlobal, pattern RegionBottom, pattern RegionLocal
  , weakenRegionVar, strengthenRegionVar
  , RegionVars(..)
  , regionVarsSize, flattenRegionVars, mapRegionVars, mapRegionVarsM
  , regionSortSize, bindRegionVars, zipFlattenRegionVars
  , showRegionVarsWith, regionSortToVars, regionSortToLevels
  , rnfRegionVars
  ) where

import Data.List

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Utils

newtype RegionVar = RegionVar { regionVarIndex :: Int }
  deriving (Eq, Ord)

instance Show RegionVar where
  show RegionGlobal = "ρ_global"
  show RegionBottom = "ρ_bottom"
  show (RegionLocal i) = 'ρ' : showSubscript i

pattern RegionGlobal :: RegionVar
pattern RegionGlobal = RegionVar 0xFFFFFFFF

pattern RegionBottom :: RegionVar
pattern RegionBottom = RegionVar 0xFFFFFFFE

pattern RegionLocal :: Int -> RegionVar
pattern RegionLocal idx <- RegionVar (localIdx -> Just idx)
  where
    RegionLocal idx = RegionVar idx

{-# COMPLETE RegionGlobal, RegionBottom, RegionLocal #-}

localIdx :: Int -> Maybe Int
localIdx i
  | i < 0xFFFFFFFE = Just i
  | otherwise = Nothing

weakenRegionVar :: Int -> Int -> RegionVar -> RegionVar
weakenRegionVar first k (RegionLocal idx) = RegionLocal $ weakenIndex first k idx
weakenRegionVar _ _ r = r -- Global or bottom region

strengthenRegionVar :: Int -> Int -> RegionVar -> Maybe RegionVar
strengthenRegionVar first k (RegionLocal idx) = RegionLocal <$> strengthenIndex first k idx
strengthenRegionVar _ _ r = Just r -- Global or bottom region

data RegionVars
  = RegionVarsSingle !RegionVar
  | RegionVarsTuple ![RegionVars]
  deriving (Eq, Ord)

regionVarsSize :: RegionVars -> Int
regionVarsSize (RegionVarsSingle _) = 1
regionVarsSize (RegionVarsTuple vars) = sum $ map regionVarsSize vars

regionSortSize :: RegionSort -> Int
regionSortSize (RegionSortForall _ s) = regionSortSize s
regionSortSize RegionSortMonomorphic = 1
regionSortSize (RegionSortPolymorphic _ _) = 1
regionSortSize (RegionSortTuple sorts) = sum $ map regionSortSize sorts

flattenRegionVars :: RegionVars -> [RegionVar]
flattenRegionVars = (`go` [])
  where
    go :: RegionVars -> [RegionVar] -> [RegionVar]
    go (RegionVarsSingle var) xs = var : xs
    go (RegionVarsTuple vars) xs = foldr go xs vars

mapRegionVars :: (RegionVar -> RegionVar) -> RegionVars -> RegionVars
mapRegionVars f (RegionVarsSingle var) = RegionVarsSingle $ f var
mapRegionVars f (RegionVarsTuple vars) = RegionVarsTuple $ map (mapRegionVars f) vars

mapRegionVarsM :: Applicative m => (RegionVar -> m RegionVar) -> RegionVars -> m RegionVars
mapRegionVarsM f (RegionVarsSingle var) = RegionVarsSingle <$> f var
mapRegionVarsM f (RegionVarsTuple vars) = RegionVarsTuple <$> traverse (mapRegionVarsM f) vars

bindRegionVars :: (RegionVar -> RegionVars) -> RegionVars -> RegionVars
bindRegionVars f (RegionVarsSingle var) = f var
bindRegionVars f (RegionVarsTuple vars) = RegionVarsTuple $ map (bindRegionVars f) vars

showRegionVarsWith :: (RegionVar -> String) -> RegionVars -> ShowS
showRegionVarsWith f (RegionVarsSingle var) = showString $ f var
showRegionVarsWith f (RegionVarsTuple vars) = showListWith "(" ")" (showRegionVarsWith f) vars

instance Show RegionVars where
  showsPrec _ = showRegionVarsWith show

regionSortToVars :: Int -> RegionSort -> RegionVars
regionSortToVars firstIdx' r' = snd $ go firstIdx' r'
  where
    go :: Int -> RegionSort -> (Int, RegionVars)
    go firstIdx RegionSortMonomorphic = (firstIdx + 1, RegionVarsSingle $ RegionLocal firstIdx)
    go firstIdx RegionSortPolymorphic{} = (firstIdx + 1, RegionVarsSingle $ RegionLocal firstIdx)
    go firstIdx (RegionSortTuple rs) = RegionVarsTuple <$> mapAccumR go firstIdx rs
    go firstIdx (RegionSortForall _ r) = go firstIdx r

regionSortToLevels :: Int -> RegionSort -> (Int, RegionVars)
regionSortToLevels firstLevel RegionSortMonomorphic = (firstLevel + 1, RegionVarsSingle $ RegionLocal firstLevel)
regionSortToLevels firstLevel RegionSortPolymorphic{} = (firstLevel + 1, RegionVarsSingle $ RegionLocal firstLevel)
regionSortToLevels firstLevel (RegionSortTuple rs) = RegionVarsTuple <$> mapAccumL regionSortToLevels firstLevel rs
regionSortToLevels firstLevel (RegionSortForall _ r) = regionSortToLevels firstLevel r

-- Assumes that the two region vars have a similar shape, but it allows that one side
-- has a single region var (monomorphic or polymorphic) where the other has a tuple.
zipFlattenRegionVars :: (RegionVar -> RegionVar -> a) -> RegionVars -> RegionVars -> [a]
zipFlattenRegionVars f varsLeft varsRight = go varsLeft varsRight []
  where
    go (RegionVarsSingle var) vars = (map (f var) (flattenRegionVars vars) ++)
    go vars (RegionVarsSingle var) = (map (`f` var) (flattenRegionVars vars) ++)
    go (RegionVarsTuple vars) (RegionVarsTuple vars') = goList vars vars'

    goList [] [] = id
    goList (v:vs) (v':vs') = go v v' . goList vs vs'
    goList _ _ = error "Helium.CodeGeneration.Iridium.Region.RegionVars.zipFlattenRegionVars: Region vars mismatch"

rnfRegionVars :: RegionVars -> ()
rnfRegionVars (RegionVarsSingle _) = ()
rnfRegionVars (RegionVarsTuple vars) = foldl' seq () $ map rnfRegionVars vars
