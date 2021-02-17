module Helium.CodeGeneration.Iridium.RegionSize.Sort
where

import Helium.CodeGeneration.Iridium.RegionSize.Utils

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

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Show Sort where
    show (SortLam        a b  ) = show a ++ " ↦  " ++ show b
    show (SortConstr          ) = "C"
    show (SortUnit            ) = "()"
    show (SortQuant      _ s  ) = "forall α. " ++ show s
    show (SortMonoRegion      ) = "P"
    show (SortPolyRegion v  _ ) = "P<" ++ show v ++ ">"
    show (SortPolySort   v  _ ) = "Ψ<" ++ show v ++ ">"
    show (SortTuple      ss   ) = "(" ++ (intercalate "," $ map show ss) ++ ")" 

----------------------------------------------------------------
-- Sort algebra
----------------------------------------------------------------

-- | Algebra for sorts
data SortAlg a = 
  SortAlg { 
    sortLam        :: a -> a -> a,
    sortConstr     :: a,
    sortUnit       :: a,
    sortQuant      :: Quantor -> a -> a,
    sortMonoRegion :: a,
    sortPolyRegion :: TypeVar -> [Type] -> a,
    sortPolySort   :: TypeVar -> [Type] -> a,
    sortTuple      :: [a] -> a
  }

-- | Algebra that does not change the sort, usefull to edit for specific cases 
idSortAlg :: SortAlg Sort
idSortAlg = SortAlg {
  sortLam        = SortLam, 
  sortConstr     = SortConstr, 
  sortUnit       = SortUnit, 
  sortQuant      = SortQuant, 
  sortMonoRegion = SortMonoRegion, 
  sortPolyRegion = SortPolyRegion, 
  sortPolySort   = SortPolySort, 
  sortTuple      = SortTuple  
}

-- | Execute a sort algebra on a sort
execSortAlg :: SortAlg a -> Sort -> a
execSortAlg alg = go
  where go (SortLam        a b ) = sortLam alg (go a) (go b)
        go (SortConstr         ) = sortConstr alg
        go (SortUnit           ) = sortUnit   alg
        go (SortQuant      a s ) = sortQuant      alg a $ go s
        go (SortMonoRegion     ) = sortMonoRegion alg
        go (SortPolyRegion a ts) = sortPolyRegion alg a ts  
        go (SortPolySort   a ts) = sortPolySort   alg a ts
        go (SortTuple      ss  ) = sortTuple      alg $ map (go) ss

----------------------------------------------------------------
-- Sort utilities
----------------------------------------------------------------

-- | TODO: Sort assign
-- sortAssign :: Type -> Sort
-- sortAssign (TAp a b) = 

-- | Instatiate a quantified type in a sort
sortInstantiate :: Quantor -> Type -> Sort -> Sort
sortInstantiate quant t = execSortAlg instAlg
  where instAlg = idSortAlg {
    sortPolyRegion = undefined, -- \a ts -> regionAssign $ typeInstantiate t ts, -- TODO: What if a != quant and extra polymorphic arguments in ts
    sortPolySort   = undefined  -- \a ts -> sortAssign   $ typeInstantiate t ts  -- TODO: What if a != quant and extra polymorphic arguments in ts
  }

typeInstantiate :: Type -> [Type] -> Type
typeInstantiate t [] = t 
typeInstantiate _ _ = rsError "Datatypes not implemented yet"


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