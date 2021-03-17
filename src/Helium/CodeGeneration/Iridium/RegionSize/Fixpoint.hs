module Helium.CodeGeneration.Iridium.RegionSize.Fixpoint
where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate

-- | Solve a fixpoint
solveFix :: Annotation -> Annotation
solveFix fix@(AFix s a) = 
    let isFix = countFixBinds fix > 0
    in if not isFix
       then a
       else iterate 0 (ABot s)
    where iterate :: Int -> Annotation -> Annotation
          iterate 3 x = AFix s x
          iterate n x = let res = eval $ AApl (ALam s a) x
                        in if res == x
                           then res
                           else iterate (n+1) res


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
