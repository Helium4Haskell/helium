module Helium.CodeGeneration.Iridium.RegionSize.Test
where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.Map as M

-- | Application of annotations
-- application (ALam SortMonoRegion $ AConstr $ M.fromList [(RegVar 0, 1)]) (AReg 1)
-- (E.eval $ application (application (A.ALam (SortLam SortUnit SortUnit) $ A.ALam SortUnit $ (A.AApl (A.AVar 1) (A.AVar 0))) (A.ALam (SortUnit) A.AUnit)) A.AUnit) == A.AUnit
-- let f = (A.ALam (SortLam SortConstr SortConstr) (AApl (A.AVar 0) (AConstr $ M.fromList [(RegVar 0, 1)])))
-- let x = (A.ALam SortConstr (AAdd (A.AVar 0) (AConstr $ M.fromList [(RegVar 0, 1)])))
-- (ALam SortMonoRegion )

regApl1 = AApl (ALam SortMonoRegion $ AConstr $ M.fromList [(RegVar 1, 1)]) (AReg 1)

-- Simple application
regApl2 = ALam SortMonoRegion (AApl (ALam SortMonoRegion $ AConstr $ M.fromList [(RegVar 1, 1), (RegVar 2, 1)]) (AReg 1))
regApl3 = AApl (ALam SortMonoRegion (ALam SortMonoRegion $ AConstr $ M.fromList [(RegVar 1, 1), (RegVar 2, 1)])) (AReg 1)

-- Weaking and reindexing at the same time
-- regApl4 == (\ψ:P.(\ψ:P.{r$1 ↦  1} ⊕  {r$2 ↦  1}))
regApl4 = let ho = (ALam (SortLam SortConstr SortConstr) (AApl (AVar 1) (mkAConstr True 2)))
              f  = ALam (SortConstr) (ALam SortMonoRegion (AAdd (mkAConstr True 1) (AVar 2)))
          in ALam sortRegionTuple $ AApl ho f

-- Weakening
-- regApl6 = (\ψ:().(\ψ:().(\ψ:().v$3)))
regApl5 = ALam SortUnit (AApl (ALam SortUnit $ ALam SortUnit $ AVar 2) (ALam SortUnit $ AVar 2))

regApl6 = AApl regApl4 $ ATuple [AReg 2, AReg 3, AReg 4] 

sortRegionTuple = (SortTuple [SortMonoRegion, SortMonoRegion]) 


mkAConstr :: Bool -- Var? 
          -> Int -> Annotation
mkAConstr True  idx = AConstr $ M.fromList [(RegVar idx, 1)]
mkAConstr False idx = AConstr $ M.fromList [(Region idx, 1)]


