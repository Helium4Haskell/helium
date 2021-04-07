{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.Region.Sort
  ( TypeVar, showSubscript, LifetimeContext(..)
  , Sort(..), pattern SortUnit
  , RegionSort(..), pattern RegionSortUnit
  , showSort, showSortLow, showRegionSort, sortReindex, regionSortReindex
  , sortWeaken, sortWeaken', sortStrengthen, sortStrengthen'
  , regionSortWeaken, regionSortWeaken', regionSortStrengthen, regionSortStrengthen'
  , showRegionSortWithVariables, rnfSort, rnfRegionSort
  ) where

import Lvm.Core.Type
import Data.List
import Data.Functor.Identity

import Helium.CodeGeneration.Iridium.Region.Utils

data LifetimeContext
  -- Argument may only be used on the right hand side of the >=,
  -- ie it may only be used to increase the life times of other regions.
  = LifetimeContextLocalBottom
  -- Argument may be used on both sides of >=.
  | LifetimeContextAny
  deriving (Eq, Ord)

instance Show LifetimeContext where
  show LifetimeContextLocalBottom = "⥜"
  show LifetimeContextAny = ""

data Sort
  = SortForall !Quantor !Sort
  | SortFun !Sort !RegionSort !LifetimeContext !Sort
  | SortTuple ![Sort]
  | SortRelation
  | SortPolymorphic !TypeVar ![Type]
  deriving (Eq, Ord)

pattern SortUnit :: Sort
pattern SortUnit = SortTuple []

data RegionSort
  = RegionSortForall !Quantor !RegionSort
  | RegionSortMonomorphic
  | RegionSortPolymorphic !TypeVar ![Type]
  | RegionSortTuple ![RegionSort]
  deriving (Eq, Ord)

pattern RegionSortUnit :: RegionSort
pattern RegionSortUnit = RegionSortTuple []

sortWeaken :: Int -> Sort -> Sort
sortWeaken 0 = id
sortWeaken k = sortReindex (k+)

sortWeaken' :: Int -> Int -> Sort -> Sort
sortWeaken' _ 0 = id
sortWeaken' first k = sortReindex (weakenIndex first k)

sortStrengthen :: Int -> Sort -> Maybe Sort
sortStrengthen = sortStrengthen' 0

sortStrengthen' :: Int -> Int -> Sort -> Maybe Sort
sortStrengthen' _ 0 = Just
sortStrengthen' first k = sortReindexM (strengthenIndex first k)

sortReindex :: (TypeVar -> TypeVar) -> Sort -> Sort
sortReindex f s = runIdentity $ sortReindexM (Identity . f) s

sortReindexM :: Applicative m => (TypeVar -> m TypeVar) -> Sort -> m Sort
sortReindexM f = go 0
  where
    go forallCount (SortForall quantor s) = SortForall quantor <$> go (forallCount+1) s
    go forallCount (SortFun argAnnotation argRegion dir a) =
      SortFun
        <$> go forallCount argAnnotation
        <*> (regionSortReindexM (f' forallCount) argRegion)
        <*> pure dir
        <*> go forallCount a
    go forallCount (SortTuple sorts) = SortTuple <$> traverse (go forallCount) sorts
    go _ SortRelation = pure SortRelation
    go forallCount (SortPolymorphic tvar tps) =
      SortPolymorphic <$> f' forallCount tvar <*> traverse (typeReindexM $ f' forallCount) tps

    -- Weaken function 'f' by 'forallCount'
    f' forallCount x
      | x < forallCount = pure x
      | otherwise = (forallCount +) <$> f (x - forallCount)

regionSortWeaken :: Int -> RegionSort -> RegionSort
regionSortWeaken 0 = id
regionSortWeaken k = regionSortReindex (k+)

regionSortWeaken' :: Int -> Int -> RegionSort -> RegionSort
regionSortWeaken' _ 0 = id
regionSortWeaken' forallCount k = regionSortReindex (weakenIndex forallCount k) 

regionSortStrengthen :: Int -> RegionSort -> Maybe RegionSort
regionSortStrengthen = regionSortStrengthen' 0

regionSortStrengthen' :: Int -> Int -> RegionSort -> Maybe RegionSort
regionSortStrengthen' _ 0 = Just
regionSortStrengthen' first k = regionSortReindexM (strengthenIndex first k)

regionSortReindex :: (TypeVar -> TypeVar) -> RegionSort -> RegionSort
regionSortReindex f s = runIdentity $ regionSortReindexM (Identity . f) s

regionSortReindexM :: Applicative m => (TypeVar -> m TypeVar) -> RegionSort -> m RegionSort
regionSortReindexM f = go 0
  where
    go forallCount (RegionSortForall _ rs)       = go (forallCount + 1) rs
    go _            RegionSortMonomorphic        = pure RegionSortMonomorphic
    go forallCount (RegionSortPolymorphic v tps) =
      RegionSortPolymorphic <$> f v <*> traverse (typeReindexM (f' forallCount)) tps
    go forallCount (RegionSortTuple sorts)       = RegionSortTuple <$> traverse (go forallCount) sorts

    -- Weaken function 'f' by 'forallCount'
    f' forallCount x
      | x < forallCount = pure x
      | otherwise = (forallCount +) <$> f (x - forallCount)

showSort :: QuantorNames -> Sort -> ShowS
showSort quantors (SortForall quantor sort1) s
  = "∀ " ++ quantorName ++ ". " ++ showSort (quantorName : quantors) sort1 s
  where
    quantorName = freshQuantorName quantors quantor
showSort quantors (SortFun sortArg RegionSortUnit _ sort1) s
  = showSortLow quantors sortArg $ " -> " ++ showSort quantors sort1 s
showSort quantors (SortFun sortArg regionArgs dir sort1) s
  = "[" ++ showSort quantors sortArg ("; " ++ (showRegionSort quantors) regionArgs ("]" ++ show dir ++ " -> " ++ showSort quantors sort1 s))
showSort quantors sort' s = showSortLow quantors sort' s

showSortLow :: QuantorNames -> Sort -> ShowS
showSortLow _ SortRelation s = 'R' : s
showSortLow quantors (SortPolymorphic tvar tps) s = "Ψ⟨" ++ showTypeVar quantors tvar ++ (tps >>= (\tp -> " " ++ showTypeAtom quantors tp)) ++ "⟩" ++ s
showSortLow quantors (SortTuple sorts) s = showListWith (if single sorts then "T(" else "(") ")" (showSort quantors) sorts s
  where
    single [_] = True
    single _ = False
showSortLow quantors sort1 s = "(" ++ showSort quantors sort1 (')' : s)

showRegionSort :: QuantorNames -> RegionSort -> ShowS
showRegionSort quantors (RegionSortForall quantor sort1) s
  = "∀ " ++ quantorName ++ ". " ++ showRegionSort (quantorName : quantors) sort1 s
  where
    quantorName = freshQuantorName quantors quantor
showRegionSort _ RegionSortMonomorphic s = 'Ρ' : s
showRegionSort quantors (RegionSortPolymorphic tvar tps) s = "Ρ⟨" ++ showTypeVar quantors tvar ++ (tps >>= (\tp -> " " ++ showTypeAtom quantors tp)) ++ "⟩" ++ s
showRegionSort quantors (RegionSortTuple sorts) s = showListWith "(" ")" (showRegionSort quantors) sorts s
  where
    single [_] = True
    single _ = False

showRegionSortWithVariables :: QuantorNames -> [String] -> RegionSort -> ShowS
showRegionSortWithVariables quantors names regionSort = snd $ showRegionSortWithVariables' quantors names regionSort

showRegionSortWithVariables' :: QuantorNames -> [String] -> RegionSort -> ([String], ShowS)
showRegionSortWithVariables' quantors names (RegionSortForall quantor sort1)
  = (names', \s -> "∀ " ++ quantorName ++ ". " ++ body s)
  where
    (names', body) = showRegionSortWithVariables' (quantorName : quantors) names sort1
    quantorName = freshQuantorName quantors quantor
showRegionSortWithVariables' _        (name:names) RegionSortMonomorphic = (names, \s -> name ++ ": Ρ" ++ s)
showRegionSortWithVariables' quantors (name:names) (RegionSortPolymorphic tvar tps) =
  (names, \s -> name ++ ": Ρ⟨" ++ showTypeVar quantors tvar ++ (tps >>= (\tp -> " " ++ showTypeAtom quantors tp)) ++ "⟩" ++ s)
showRegionSortWithVariables' _        names (RegionSortTuple []) = (names, showString "()")
showRegionSortWithVariables' quantors names (RegionSortTuple (rs:rss)) =
  (names'', showString "(" . headS . tailS)
  where
    (names', headS) = showRegionSortWithVariables' quantors names rs
    (names'', tailS) = go names' rss

    go :: [String] -> [RegionSort] -> ([String], ShowS)
    go names1 [] = (names1, showString ")")
    go names1 (rs':rss') = (names3, showString ", " . s . s')
      where
        (names2, s) = showRegionSortWithVariables' quantors names1 rs'
        (names3, s') = go names2 rss'
showRegionSortWithVariables' _ [] _ = error "showRegionSortWithVariables: Not enough variables"

rnfSort :: Sort -> ()
rnfSort (SortForall _ s) = rnfSort s
rnfSort (SortFun s1 rs _ s2) = rnfSort s1 `seq` rnfRegionSort rs `seq` rnfSort s2
rnfSort (SortTuple sorts) = foldl' seq () $ map rnfSort sorts
rnfSort SortRelation = ()
rnfSort (SortPolymorphic _ tps) = foldl' (flip seq) () tps

rnfRegionSort :: RegionSort -> ()
rnfRegionSort (RegionSortForall _ rs) = rnfRegionSort rs
rnfRegionSort (RegionSortTuple regionSorts) = foldl' seq () $ map rnfRegionSort regionSorts
rnfRegionSort RegionSortMonomorphic = ()
rnfRegionSort (RegionSortPolymorphic _ tps) = foldl' (flip seq) () tps
