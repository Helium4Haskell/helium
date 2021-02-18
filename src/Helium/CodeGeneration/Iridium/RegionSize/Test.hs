module Helium.CodeGeneration.Iridium.RegionSize.Test
where

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.Map as M

-- | Application of annotations
-- application (ALam SortMonoRegion $ AConstr $ M.fromList [(ReV 0, 1)]) (AReg 1)
-- (E.eval $ application (application (A.ALam (SortLam SortUnit SortUnit) $ A.ALam SortUnit $ (A.AApl (A.AVar 1) (A.AVar 0))) (A.ALam (SortUnit) A.AUnit)) A.AUnit) == A.AUnit
-- let f = (A.ALam (SortLam SortConstr SortConstr) (AApl (A.AVar 0) (AConstr $ M.fromList [(ReV 0, 1)])))
-- let x = (A.ALam SortConstr (AAdd (A.AVar 0) (AConstr $ M.fromList [(ReV 0, 1)])))
-- (ALam SortMonoRegion )

regApl1 = AApl (ALam SortMonoRegion $ AConstr $ M.fromList [(ReV 1, 1)]) (AReg 1)
regApl2 = ALam SortMonoRegion (AApl (ALam SortMonoRegion $ AConstr $ M.fromList [(ReV 1, 1), (ReV 2, 1)]) (AReg 1))
regApl5 = AApl (ALam SortMonoRegion (ALam SortMonoRegion $ AConstr $ M.fromList [(ReV 1, 1), (ReV 2, 1)])) (AReg 1)


-- regApl3 == (\ψ:P.(\ψ:P.{p_r$0 ↦  1, p_r$1 ↦  1}))
regApl3 = let ho = (ALam (SortLam SortConstr SortConstr) (AApl (AVar 1) (mkAConstr True 2)))
              f  = ALam (SortConstr) (ALam SortMonoRegion (AAdd (mkAConstr True 1) (AVar 2)))
          in ALam SortMonoRegion $ AApl ho f

-- regApl4 == {p_rho_1337 ↦  1, p_rho_4200 ↦  1}
regApl4 = AApl (AApl regApl3 (AReg 1337)) (AReg 4200)

mkAConstr :: Bool -- Var? 
          -> Int -> Annotation
mkAConstr True  idx = AConstr $ M.fromList [(ReV idx, 1)]
mkAConstr False idx = AConstr $ M.fromList [(Reg idx, 1)]


