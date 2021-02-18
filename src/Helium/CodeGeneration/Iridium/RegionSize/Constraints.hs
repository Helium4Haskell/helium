module Helium.CodeGeneration.Iridium.RegionSize.Constraints
where

import qualified Data.Map as M

type RegVar = Int
type Region = Int

data ConstrIdx = ReV RegVar
               | Reg Region
    deriving (Eq,Ord)

instance Show ConstrIdx where
    show (ReV idx) = "r$" ++ show idx
    show (Reg idx) = "rho_" ++ show idx

type Constr = M.Map ConstrIdx Int

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
           -> RegVar -- ^ The region variable to instantiate 
           -> Constr -> Constr
constrInst inst r c = constrAdd inst $ constrRem (ReV r) c
