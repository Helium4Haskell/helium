module Helium.CodeGeneration.Iridium.RegionSize.Constraints
    (ConstrIdx(..), Constr, Bound(..),
    constrShow, constrIdxShow,
    constrReIndex, constrWeaken, constrStrengthen, constrStrengthenN,
    constrIdxStrengthenN,
    constrIdxWithVar, constrIdx, 
    constrBot, constrJoin, constrJoins, 
    constrAdd, constrAdds,
    constrRem, constrRemVar,
    constrOne, constrInfty,
    constrRemLocalRegs, constrRemVarRegs)
where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Parameters

import qualified Data.Map.Strict as M
import Data.List

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

type Depth = Int
type Index = Int

data ConstrIdx = AnnVar Index         -- ^ Annotation variable
               | CnProj Int ConstrIdx -- ^ Project on region tuple
               | Region RegionVar     -- ^ Region variable 
    deriving (Eq, Ord)

data Bound = Nat Int | Infty
    deriving (Eq, Ord)

type Constr = M.Map ConstrIdx Bound

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Show Bound where
    show (Nat n) = show n
    show (Infty) = "∞"

instance Show ConstrIdx where
    show = constrIdxShow (-1)

constrShow :: Depth -> Constr -> String
constrShow d c = "{" ++ (intercalate ", " $ map (\(x, b) -> constrIdxShow d x ++ " ↦  " ++ show b) $ M.toList c) ++ "}"

constrIdxShow :: Depth -> ConstrIdx -> String
constrIdxShow d (AnnVar idx) = annVarName (d - idx) 
constrIdxShow d (CnProj i c) = constrIdxShow d c ++ "." ++ show i 
constrIdxShow _ (Region var) = show var 

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------

-- | Re-index the debruijn indices of a cosntraint set 
constrReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
              -> Int -- ^ Depth of constraint set in annotation
              -> Constr -> Constr
constrReIndex f d = M.mapKeys (constrIdxReIdx f d)

-- | Increase constraint set indices by subtitution depth
constrWeaken :: Int -> Constr -> Constr
constrWeaken n = constrReIndex (weakenIdx n) (-1)

-- | Decrease all unbound de bruijn indeces by 1
constrStrengthen :: Constr -> Constr
constrStrengthen = constrStrengthenN (-1)

-- | Decrease all unbound de bruijn indeces by 1, starting at depth N
constrStrengthenN :: Int -> Constr -> Constr
constrStrengthenN = constrReIndex strengthenIdx

-- | Reindex the keys of a cosntraint set
constrIdxReIdx :: (Depth -> Int -> Int) -- ^ Reindex function
               -> Int -- ^ Depth of constraint set in annotation
               -> ConstrIdx -> ConstrIdx
constrIdxReIdx f d (AnnVar idx) = AnnVar $ f d idx
constrIdxReIdx f d (CnProj i c) = CnProj i $ constrIdxReIdx f d c 
constrIdxReIdx _ _ (Region var) = Region var

-- | Increase all unbound indexes by 1
constrIdxStrengthenN :: Int -> ConstrIdx -> ConstrIdx
constrIdxStrengthenN = constrIdxReIdx strengthenIdx

----------------------------------------------------------------
-- Constraint utilities
----------------------------------------------------------------

-- | Constraint bottom, also empty constraint set
constrBot :: Constr
constrBot = M.empty


-- | Join of constraint sets
constrJoin :: Constr -> Constr -> Constr
constrJoin = M.unionWith boundMax
    where 
        boundMax :: Bound -> Bound -> Bound
        boundMax Infty _ = Infty
        boundMax _ Infty = Infty
        boundMax (Nat a) (Nat b) = Nat $ max a b

-- | Join of constraint sets
constrJoins :: [Constr] -> Constr
constrJoins = foldr constrJoin constrBot


-- | Addition of constraint sets
constrAdd :: Constr -> Constr -> Constr
constrAdd = M.unionWith boundAdd
    where 
        boundAdd :: Bound -> Bound -> Bound
        boundAdd Infty _ = Infty
        boundAdd _ Infty = Infty
        boundAdd (Nat a) (Nat b) = if a + b > max_bound
                                   then Infty
                                   else Nat $ a + b

-- | Addition of a list of constraint sets
constrAdds :: [Constr] -> Constr
constrAdds = foldr constrAdd constrBot


-- | Index a constraint set (default 0)
constrIdx :: ConstrIdx -> Constr -> Bound
constrIdx = M.findWithDefault (Nat 0)

-- | Get all constraint indexes that use a variable
constrIdxWithVar :: Int -> Constr -> [ConstrIdx] 
constrIdxWithVar idx = filter f . M.keys  
    where f (AnnVar var) = idx == var
          f (CnProj _ c) = f c 
          f _ = False 

-- | Remove a region variable from the constraint set
constrRem :: ConstrIdx -> Constr -> Constr
constrRem = M.delete

-- | Remove a region variable from the constraint set
constrRemVar :: Int -> Constr -> Constr
constrRemVar idx = M.filterWithKey go
    where go (CnProj i idx') _ = go idx' undefined
          go (Region _)      _ = True  
          go (AnnVar idx')   _ = idx /= idx'  

-- | Create a constraint set for a single variable
constrOne :: ConstrIdx -> Constr
constrOne i = M.singleton i $ Nat 1

-- | Create a constraint set for a single variable
constrInfty :: ConstrIdx -> Constr
constrInfty i = M.singleton i $ Infty

-- | Remove local regions from constraint set
constrRemLocalRegs :: Constr -> Constr
constrRemLocalRegs = M.filterWithKey (\k _ -> not$isLocalRegion k)

-- | Remove local regions from constraint set
constrRemVarRegs :: Constr -> Constr
constrRemVarRegs = M.filterWithKey (\k _ -> isLocalRegion k)

-- | Check if constraintidx points to a local region
isLocalRegion :: ConstrIdx -> Bool
isLocalRegion (Region RegionGlobal) = False
isLocalRegion (Region _           ) = True
isLocalRegion _ = False
