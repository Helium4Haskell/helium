module Helium.CodeGeneration.Iridium.RegionSize.Fixpoint
where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate

-- | Solve all the fixpoints in an annotation
solveFixpoints :: Annotation -> Annotation
solveFixpoints = eval . fillTop . foldAnnAlg fixAlg
    where fixAlg = idAnnAlg {
        aFix = \_ s as -> ATuple $ solveFixpoint s as
    }

-- | Solve a group of fixpoints
solveFixpoint :: Sort -> [Annotation] -> [Annotation]
solveFixpoint s fixes = 
        let bot = ABot s
        in fixIterate 0 bot fixes
    where fixIterate :: Int -> Annotation -> [Annotation] -> [Annotation]
          fixIterate 10 _     _  = mapWithIndex (\ i _ -> AProj i $ ATop s constrBot) fixes
          fixIterate n  state fs = 
              let res = (\fix -> eval $ AApl (ALam s fix) state) <$> fs
              in if ATuple res == state
                 then res
                 else fixIterate (n+1) (ATuple res) fs

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
        aTop    = \_ _ _ -> 0, -- TODO: Count rec references in top?
        aBot    = \_ _   -> 0,
        aFix    = \_ _ a -> sum a   
    }

-- | Fill top with local variables in scope
fillTop :: Annotation -> Annotation
fillTop = go constrBot
    where go scope (ATop   s c) = ATop s $ constrAdd c scope
          go scope (ALam   s a) | sortIsRegion s = ALam s $ go (constrAdd (constrInfty $ AnnVar 0) (constrWeaken 1 scope)) a  
                                | otherwise      = ALam s $ go (constrWeaken 1 scope) a
          go scope (ATuple  as) = ATuple $ go scope <$> as
          go scope (AProj  i a) = AProj i $ go scope a 
          go scope (AApl   a b) = AApl   (go scope a) (go scope b) 
          go scope (AAdd   a b) = AAdd   (go scope a) (go scope b)  
          go scope (AMinus a r) = AMinus (go scope a) r
          go scope (AJoin  a b) = AJoin  (go scope a) (go scope b)
          go scope (AQuant a  ) = AQuant (go scope a)
          go scope (AInstn a t) = AInstn (go scope a) t
          go scope (AFix   s v) = AFix s $ go scope <$> v
          go _     ann = ann
