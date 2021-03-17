module Helium.CodeGeneration.Iridium.RegionSize.Fixpoint
where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate

-- TODO: Do a monotone-framework style iterate-when-depency chagned thing

-- | Solve a group of fixpoints
solveFixpoints :: [Annotation] -> [Annotation]
solveFixpoints fixes = 
        let init = map (\(AFix s _) -> ABot s) fixes
        in iterate 0 init fixes
    where iterate :: Int -> [Annotation] -> [Annotation] -> [Annotation]
          iterate 10 state fs = state
          iterate n  state fs = 
              let res = solveFix (ATuple state) <$> fs
              in if res == state 
                 then res
                 else iterate (n+1) res fs

-- | Solve a fixpoint
solveFix :: Annotation -- ^ The state
         -> Annotation -- ^ The fixpoint
         -> Annotation
solveFix x fix@(AFix s a) = 
    let isFixpoint = countFixBinds fix > 0
    in if not isFixpoint
       then a
       else eval $ AApl (ALam s a) x
solveFix x _ = x

-- | Count usages of a variable
countFixBinds :: Annotation -> Int
countFixBinds = foldAnnAlg countAlg
    where countAlg = AnnAlg {
        aVar    = \d idx -> if d == idx then 1 else 0,
        aReg    = \_ _   -> 0,
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> a + b,
        aConstr = \_ _   -> 0,
        aUnit   = \_     -> 0,
        aTuple  = \_ as  -> sum as,
        aProj   = \_ _ a -> a,
        aAdd    = \_ a b -> a + b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> a + b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \_ _   -> 0,
        aBot    = \_ _   -> 0,
        aFix    = \_ _ a -> a   
    }
