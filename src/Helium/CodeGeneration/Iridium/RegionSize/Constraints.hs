module Helium.CodeGeneration.Iridium.RegionSize.Constraints
    (ConstrIdx(..), Constr, 
    constrShow, constrIdxShow,
    constrReIndex, constrIdxWithVar,
    constrBot, constrJoin, constrAdd, constrIdx, constrRem, constrInst, constrOne)
where

import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map as M
import Data.List

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

type Depth = Int
type Index = Int
data ConstrIdx = AnnVar Index         -- ^ Annotation variable
               | CnProj Int ConstrIdx -- ^ Project on annotation tuple
    deriving (Eq, Ord)
type Constr = M.Map ConstrIdx Int

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

constrShow :: Depth -> Constr -> String
constrShow d c = "{" ++ (intercalate ", " $ map (\(x, b) -> constrIdxShow d x ++ " ↦  " ++ show b) $ M.toList c) ++ "}"

constrIdxShow :: Depth -> ConstrIdx -> String
constrIdxShow d (AnnVar idx) = annVarName (d - idx - 1) 
constrIdxShow d (CnProj i c) = constrIdxShow d c ++ "." ++ show i 

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
constrOne :: Maybe ConstrIdx -> Constr
constrOne (Just i) = M.singleton i 1
constrOne (Just i) = M.empty