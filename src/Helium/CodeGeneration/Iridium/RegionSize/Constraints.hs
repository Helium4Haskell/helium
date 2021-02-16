module Helium.CodeGeneration.Iridium.RegionSize.Constraints
where

import qualified Data.Map as M

type RegVar = Int
type Constr = M.Map RegVar Int

-- | Join of constraint sets
constrJoin :: Constr -> Constr -> Constr
constrJoin = M.unionWith max

-- | Addition of constraint sets
constrAdd :: Constr -> Constr -> Constr
constrAdd = M.unionWith (+)

-- | Index a constraint set (default 0)
constrIdx :: Constr -> Int -> Int
constrIdx m x = M.findWithDefault 0 x m

