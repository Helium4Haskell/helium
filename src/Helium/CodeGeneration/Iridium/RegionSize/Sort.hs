module Helium.CodeGeneration.Iridium.RegionSize.Sort
  ( Sort(..), showSort, 
    SortAlg(..), idSortAlg, foldSortAlg, foldSortAlgN, 
    sortInstantiate,
    sortIsRegion, sortIsAnnotation
  )
where

import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type

import Lvm.Core.Type
import Data.List

----------------------------------------------------------------
-- Sort
----------------------------------------------------------------

data Sort = 
      SortLam        Sort    Sort
    | SortConstr
    | SortUnit
    | SortTuple      [Sort]
    | SortQuant      Quantor Sort
    | SortMonoRegion
    | SortPolyRegion TypeVar [Type]
    | SortPolySort   TypeVar [Type]
  deriving (Eq, Ord)

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

showSort :: Depth -> Sort -> String
showSort n = foldSortAlgN n showAlg
  where showAlg = SortAlg {
    sortLam        = \_ a b  -> a ++ " ↦  " ++ b,
    sortConstr     = \_      -> "C",
    sortUnit       = \_      -> "()",
    sortQuant      = \d _ s  -> "forall " ++ show (varNames !! d) ++ ". " ++ s,
    sortMonoRegion = \_      -> "P",
    sortPolyRegion = \d idx ts -> "P<" ++ (varNames !! (d - idx)) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
    sortPolySort   = \d idx ts -> "Ψ<" ++ (varNames !! (d - idx)) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
    sortTuple      = \_ ss   -> "(" ++ (intercalate "," ss) ++ ")"
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
    sortQuant      :: Depth -> Quantor -> a -> a,
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
foldSortAlg = foldSortAlgN 0

-- | Execute a sort algebra on a sort, staring at depth N
foldSortAlgN :: Int -> SortAlg a -> Sort -> a
foldSortAlgN n alg = go n
  where go d (SortLam        a b ) = sortLam        alg d (go d a) (go d b)
        go d (SortConstr         ) = sortConstr     alg d
        go d (SortUnit           ) = sortUnit       alg d
        go d (SortQuant      a s ) = sortQuant      alg d a (go d s)
        go d (SortMonoRegion     ) = sortMonoRegion alg d
        go d (SortPolyRegion a ts) = sortPolyRegion alg d a ts  
        go d (SortPolySort   a ts) = sortPolySort   alg d a ts
        go d (SortTuple      ss  ) = sortTuple      alg d $ map (go d) ss

----------------------------------------------------------------
-- Sort utilities
----------------------------------------------------------------

-- | TODO: Sort assign
-- sortAssign :: Type -> Sort
-- sortAssign (TAp a b) = 

-- | Instatiate a quantified type in a sort
sortInstantiate :: Quantor -> Type -> Sort -> Sort
sortInstantiate quant t = foldSortAlg instAlg
  where instAlg = idSortAlg {
    sortPolyRegion = undefined, -- \a ts -> regionAssign $ typeInstantiate t ts, -- TODO: What if a != quant and extra polymorphic arguments in ts
    sortPolySort   = undefined  -- \a ts -> sortAssign   $ typeInstantiate t ts  -- TODO: What if a != quant and extra polymorphic arguments in ts
  }

-- typeInstantiate :: Type -> [Type] -> Type
-- typeInstantiate t [] = t 
-- typeInstantiate _ _ = rsError "Datatypes not implemented yet"

{-| Evaluate if a sort is a region
For sort tuples we recurse into the first element.
A sort unit is never a region (can only occur in last element of SortTuple, which we do not check)
-}
sortIsRegion :: Sort -> Bool
sortIsRegion SortMonoRegion       = True
sortIsRegion (SortPolyRegion _ _) = True
sortIsRegion (SortTuple as)       = sortIsRegion $ as !! 0
sortIsRegion _ = False

-- | Check if a sort is an annotation sort
sortIsAnnotation :: Sort -> Bool
sortIsAnnotation = not . sortIsRegion