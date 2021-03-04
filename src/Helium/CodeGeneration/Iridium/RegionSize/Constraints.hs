module Helium.CodeGeneration.Iridium.RegionSize.Constraints
    (ConstrIdx(..), Constr, 
    constrShow,
    constrReIndex,
    constrBot, constrJoin, constrAdd, constrIdx, constrRem, constrInst)
where

import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map as M
import Data.List

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

type Depth = Int
data ConstrIdx = RegVar Int
               | Region Int
    deriving (Eq, Ord)
type Constr = M.Map ConstrIdx Int

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

constrShow :: Depth -> Constr -> String
constrShow d c = "{" ++ (intercalate ", " $ map (\(x, b) -> constrIdxShow d x ++ " ↦  " ++ show b) $ M.toList c) ++ "}"

constrIdxShow :: Depth -> ConstrIdx -> String
constrIdxShow d (RegVar idx) = varNames !! (d - idx) 
constrIdxShow _ (Region idx) = "rho_" ++ show idx 

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------

-- | Re-index the debruijn indices of a cosntraint set 
constrReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
              -> Int -- ^ Depth of constraint set in annotation
              -> Constr -> Constr
constrReIndex f annD = M.mapKeys keyReIndex
  where keyReIndex (RegVar idx) = RegVar $ f annD idx
        keyReIndex (Region idx) = Region idx

----------------------------------------------------------------
-- Constraint utilities
----------------------------------------------------------------

-- | Constraint bottom, also empty constraint set
constrBot :: Constr
constrBot = M.empty

-- | Join of constraint sets
constrJoin :: Constr -> Constr -> Constr
constrJoin = M.unionWith max

-- | Addition of constraint sets
constrAdd :: Constr -> Constr -> Constr
constrAdd = M.unionWith (+)

-- | Index a constraint set (default 0)
constrIdx :: ConstrIdx -> Constr -> Int
constrIdx = M.findWithDefault 0

-- | Remove a region variable from the constraint set
constrRem :: ConstrIdx -> Constr -> Constr
constrRem = M.delete

-- | Instantiate a region variable in the constraint set
constrInst :: Constr -- ^ The instantiation
           -> Int    -- ^ The region variable to instantiate 
           -> Constr -> Constr
constrInst inst r c = constrAdd inst $ constrRem (RegVar r) c
