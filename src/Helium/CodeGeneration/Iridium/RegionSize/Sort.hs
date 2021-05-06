{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.RegionSize.Sort
  ( Sort(..), pattern SortUnit, showSort, 
    SortAlg(..), idSortAlg, foldSortAlg, foldSortAlgN)
where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type

import Lvm.Common.Id
import Lvm.Core.Type
import Data.List

----------------------------------------------------------------
-- Sort
----------------------------------------------------------------

data Sort = 
      SortLam        Sort    Sort
    | SortConstr
    | SortTuple      [Sort]
    | SortQuant      Sort
    | SortMonoRegion
    | SortPolyRegion TypeVar [Type]
    | SortPolySort   TypeVar [Type]
  deriving (Eq, Ord)

instance Show Sort where
  show s = showSort (-1) s

pattern SortUnit :: Sort
pattern SortUnit = SortTuple []

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

showSort :: Depth -> Sort -> String
showSort n = foldSortAlgN n showAlg
  where showAlg = SortAlg {
    sortLam        = \_ a b    -> "(" ++ a ++ " ↦  " ++ b ++ ")",
    sortConstr     = \_        -> "C",
    sortQuant      = \d s      -> "∀" ++ (typeVarName $ d+1) ++ ". " ++ s,
    sortMonoRegion = \_        -> "P",
    sortPolyRegion = \d idx ts -> "P<" ++ (typeVarName $ d - idx) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
    sortPolySort   = \d idx ts -> "Ψ<" ++ (typeVarName $ d - idx) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
    sortUnit       = \_        -> "TUP()",
    sortTuple      = \_ ss     -> "TUP(" ++ (intercalate "," ss) ++ ")"
}

----------------------------------------------------------------
-- Sort algebra
----------------------------------------------------------------

type Depth = Int

-- | Algebra for sorts
data SortAlg a = 
  SortAlg { 
    sortLam        :: Depth -> a -> a -> a,
    sortConstr     :: Depth -> a,
    sortUnit       :: Depth -> a,
    sortQuant      :: Depth -> a -> a,
    sortMonoRegion :: Depth -> a,
    sortPolyRegion :: Depth -> TypeVar -> [Type] -> a,
    sortPolySort   :: Depth -> TypeVar -> [Type] -> a,
    sortTuple      :: Depth -> [a] -> a
  }

-- | Algebra that does not change the sort, usefull to edit for specific cases 
idSortAlg :: SortAlg Sort
idSortAlg = SortAlg {
  sortLam        = \_ -> SortLam, 
  sortConstr     = \_ -> SortConstr, 
  sortUnit       = \_ -> SortUnit, 
  sortQuant      = \_ -> SortQuant, 
  sortMonoRegion = \_ -> SortMonoRegion, 
  sortPolyRegion = \_ -> SortPolyRegion, 
  sortPolySort   = \_ -> SortPolySort, 
  sortTuple      = \_ -> SortTuple  
}

-- | Execute a sort algebra on a sort
foldSortAlg :: SortAlg a -> Sort -> a
foldSortAlg = foldSortAlgN (-1)

-- | Execute a sort algebra on a sort, staring at depth N
foldSortAlgN :: Int -> SortAlg a -> Sort -> a
foldSortAlgN n alg = go n
  where go d (SortLam        a b ) = sortLam        alg d (go d a) (go d b)
        go d (SortConstr         ) = sortConstr     alg d
        go d (SortUnit           ) = sortUnit       alg d
        go d (SortQuant      a   ) = sortQuant      alg d (go (d+1) a)
        go d (SortMonoRegion     ) = sortMonoRegion alg d
        go d (SortPolyRegion a ts) = sortPolyRegion alg d a ts  
        go d (SortPolySort   a ts) = sortPolySort   alg d a ts
        go d (SortTuple      ss  ) = sortTuple      alg d $ map (go d) ss
