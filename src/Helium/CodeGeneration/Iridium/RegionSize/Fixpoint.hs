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

solveFixpoints :: Annotation -> Annotation
solveFixpoints = eval . foldAnnAlg fixAlg
    where fixAlg = idAnnAlg {
        aFix = \_ s as -> solveFixpoint s as
    }

-- | Solve a group of fixpoints
solveFixpoint :: Sort -> [Annotation] -> Annotation
solveFixpoint s fixes = 
        let bot = ABot s
        in iterate 0 bot fixes
    where iterate :: Int -> Annotation -> [Annotation] -> Annotation
          iterate 3 state fs = state
          iterate n  state fs = 
              let res = solveFix state SortUnit <$> fs
              in if ATuple res == state 
                 then ATuple res
                 else iterate (n+1) (ATuple res) fs

-- | Solve a fixpoint
solveFix :: Annotation -- ^ The state
         -> Sort       -- ^ Argument sort
         -> Annotation -- ^ The fixpoint
         -> Annotation
solveFix x s fix = 
    let isFixpoint = countFixBinds fix > 0
    in if not isFixpoint
       then annStrengthen fix
       else eval $ AApl (ALam s fix) x

-- | Count usages of a variable
countFixBinds :: Annotation -> Int
countFixBinds = foldAnnAlgN 0 countAlg
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
        aFix    = \_ _ a -> sum a   
    }
