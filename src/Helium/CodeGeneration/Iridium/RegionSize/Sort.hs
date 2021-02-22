module Helium.CodeGeneration.Iridium.RegionSize.Sort
  ( Sort(..), showSort, 
    SortAlg(..), idSortAlg, foldSortAlg, foldSortAlgN, 
    sortInstantiate,
    sortIsRegion, sortIsAnnotation,
    -- TODO: Remove these from exports
    sortAssign, regionAssign
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
    | SortQuant      Sort
    | SortMonoRegion
    | SortPolyRegion TypeVar [Type]
    | SortPolySort   TypeVar [Type]
  deriving (Eq, Ord)

instance Show Sort where
  show s = showSort 1 s

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

showSort :: Depth -> Sort -> String
showSort n = foldSortAlgN n showAlg
  where showAlg = SortAlg {
    sortLam        = \_ a b  -> a ++ " ↦  " ++ b,
    sortConstr     = \_      -> "C",
    sortUnit       = \_      -> "()",
    sortQuant      = \d s    -> "∀t_" ++ (varNames !! d) ++ ". " ++ s,
    sortMonoRegion = \_      -> "P",
    sortPolyRegion = \d idx ts -> "P<t_" ++ (varNames !! (d - idx)) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
    sortPolySort   = \d idx ts -> "Ψ<t_" ++ (varNames !! (d - idx)) ++ " [" ++ (intercalate "," $ map (showTypeN d) ts) ++ "]>",
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
foldSortAlg = foldSortAlgN 0

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

----------------------------------------------------------------
-- Sort assignment
----------------------------------------------------------------

-- | TODO: indexes of sort assign? Should already be bound localy?
-- | Sort assignment based on type
sortAssign :: Type -> Sort
sortAssign = sortAssign' []

-- | Sort assingment with type arguments
sortAssign' :: [Type] -- ^ Type arguments
           -> Type -> Sort
sortAssign' ts (TStrict a)     = sortAssign' ts a
sortAssign' ts (TForall _ _ a) = SortQuant $ sortAssign' ts a
sortAssign' ts (TVar a)        = SortPolySort a ts
-- Type constructors (functions, tuples, simple data types)
sortAssign' ts (TAp t1 t2)     = sortAssign' (t2:ts) t1
sortAssign' [t1,t2] (TCon TConFun)       = funSort t1 t2  
sortAssign' ts      (TCon (TConTuple n)) | length ts == n = SortTuple $ map sortAssign ts
                                         | otherwise      = rsError $ "sortAssign: Tuple with incorrect number of arguements: expected " ++ show n ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
sortAssign' []      (TCon (TConDataType _)) = SortUnit
-- Not implemented cases 
sortAssign' _ t = rsError $ "sortAssign: No pattern match: " ++ showTypeN 0 t

-- | Sort for a function: t_1 -> t2 ===> SA(t_1) -> (SA(t_2), RA(t_2) -> C)
funSort :: Type -> Type -> Sort
funSort t1 t2 = SortLam (sortAssign t1) $ SortTuple [sortAssign t2, 
                                                     SortLam (regionAssign t2) SortConstr]

----------------------------------------------------------------
-- Region assignment
----------------------------------------------------------------

-- | Region assignment based on type
regionAssign :: Type -> Sort
regionAssign ty | typeIsStrict ty = SortTuple [SortMonoRegion,                 regionAssign' [] ty]
                | otherwise       = SortTuple [SortMonoRegion, SortMonoRegion, regionAssign' [] ty]

-- | Region assingment with type arguments
regionAssign' :: [Type] -- ^ Type arguments
              -> Type -> Sort
regionAssign' ts (TVar a)        = SortPolyRegion a ts
regionAssign' ts (TStrict a)     = regionAssign' ts a
regionAssign' ts (TForall _ _ a) = SortQuant $ regionAssign' ts a
-- Type constructors (functions, tuples, simple data types)
regionAssign' ts (TAp t1 t2)     = regionAssign' (t2:ts) t1
regionAssign' [_,_] (TCon TConFun      ) = SortUnit
regionAssign' ts    (TCon (TConTuple n)) | length ts == n = SortTuple $ map regionAssign ts
                                         | otherwise      = rsError $ "regionAssign: Tuple with incorrect number of arguements: expected " ++ show n ++ " but got " ++ (show $ length ts) ++ "\n" ++ (intercalate ", " $ map (showTypeN 0) ts)
regionAssign' [] (TCon (TConDataType _)) = SortUnit
-- Not implemented cases
regionAssign' ts t = rsError $ "regionAssign: No pattern match: " ++ showTypeN 1 t 
                                  ++ "\nArguments: " ++ (intercalate ", " $ map (showTypeN 1) ts)

----------------------------------------------------------------
-- Type substitution
----------------------------------------------------------------

-- | Instatiate a quantified type in a sort
sortInstantiate :: Depth -> Type -> Sort -> Sort
sortInstantiate subD ty = foldSortAlgN subD instAlg
  where instTypeArgs d ts = map (typeInsantiate d ty) ts
        instAlg = idSortAlg {
          sortPolyRegion = \d idx ts -> if idx == d 
                                        then regionAssign' (instTypeArgs d ts) $ typeWeaken d ty
                                        else SortPolyRegion idx (instTypeArgs d ts),
          sortPolySort   = \d idx ts -> if idx == d 
                                        then sortAssign'   (instTypeArgs d ts) $ typeWeaken d ty
                                        else SortPolySort   idx (instTypeArgs d ts)
        }

----------------------------------------------------------------
-- Sort utilities
----------------------------------------------------------------

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
