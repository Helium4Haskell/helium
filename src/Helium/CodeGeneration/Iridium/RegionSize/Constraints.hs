module Helium.CodeGeneration.Iridium.RegionSize.Constraints
    (ConstrIdx(..), Constr, Bound(..),
    constrShow, constrIdxShow,
    constrReIndex, constrIdxWithVar,
    constrBot, constrJoin, constrAdd, constrIdx, constrRem, constrInst, constrOne,
    constrRemLocalRegs)
where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map as M
import Data.List

max_bound :: Int
max_bound = 3

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
constrReIndex f annD = M.mapKeys keyReIndex
  where keyReIndex (AnnVar idx) = AnnVar $ f annD idx
        keyReIndex (CnProj i c) = CnProj i $ keyReIndex c 
        keyReIndex (Region var) = Region var

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

-- | Instantiate a region variable in the constraint set
constrInst :: Constr    -- ^ The instantiation
           -> ConstrIdx -- ^ The annotation variable to instantiate 
           -> Constr -> Constr
constrInst inst idx c = constrAdd inst $ constrRem idx c

-- | Create a constraint set for a single variable
constrOne :: ConstrIdx -> Constr
constrOne i = M.singleton i $ Nat 1

-- | Remove local regions from constraint set
constrRemLocalRegs :: Constr -> Constr
constrRemLocalRegs = M.filterWithKey (\k _ -> not$isLocal k)
    where isLocal (Region RegionGlobal) = False
          isLocal (Region _           ) = True
          isLocal _ = False