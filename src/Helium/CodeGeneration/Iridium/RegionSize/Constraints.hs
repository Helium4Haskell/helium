module Helium.CodeGeneration.Iridium.RegionSize.Constraints
where

import qualified Data.Map as M

type RegVar = Int
type Region = Int 
type Constr = M.Map RegVar Int

-- | Join of constraint sets
constrJoin :: Constr -> Constr -> Constr
constrJoin = M.unionWith max

-- | Addition of constraint sets
constrAdd :: Constr -> Constr -> Constr
constrAdd = M.unionWith (+)

-- | Index a constraint set (default 0)
constrIdx :: Int -> Constr -> Int
constrIdx = M.findWithDefault 0

-- | Remove a region variable from the constraint set
constrRem :: RegVar -> Constr -> Constr
constrRem = M.delete

-- | Instantiate a region variable in the constraint set
constrInst :: Constr -- ^ The instantiation
           -> RegVar -- ^ The region variable to instantiate 
           -> Constr -> Constr
constrInst inst r c = constrAdd inst $ constrRem r c