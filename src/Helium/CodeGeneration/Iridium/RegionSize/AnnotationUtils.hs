module Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
  ( liftTuple, unliftTuple,
    collect,
    annWeaken, annStrengthen,
    isConstr, isTop, isBot, constrIdxToAnn,
    annRemLocalRegs
  ) where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map as M

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------
type Depth = Int

-- | Re-index the debruin indices of an annotation
annReIndex :: (Depth -> Int -> Int) -- ^ Reindex function (depth in body to idx to idx)
           -> Annotation -> Annotation
annReIndex f = foldAnnAlg reIdxAlg
  where reIdxAlg = idAnnAlg {
    aLam    = \d s a -> ALam (sortReIndex f d s) a,
    aFix    = \d s a -> AFix (sortReIndex f d s) a,
    aConstr = \d c   -> AConstr (constrReIndex f d c), 
    aTop    = \d s c -> ATop (sortReIndex f d s) (constrReIndex f d c), 
    aBot    = \d s   -> ABot (sortReIndex f d s), 
    aVar    = \d idx -> AVar (f d idx)
  }

-- | Increase all unbound variables by the substitution depth
annWeaken :: Depth -- ^ Depth of the substitution
          -> Annotation -> Annotation
annWeaken subD = annReIndex (weakenIdx subD)

-- | Decrease all unbound indexes by 1
annStrengthen :: Annotation -> Annotation
annStrengthen = annReIndex strengthenIdx

----------------------------------------------------------------
-- Annotation utilities
----------------------------------------------------------------

-- | Convert an annotation tuple to a haskell tuple
liftTuple :: Annotation -> (Annotation, Effect)
liftTuple a = (AProj 0 a, AProj 1 a) 

-- | Convert an annotation tuple to a haskell tuple
unliftTuple :: (Annotation, Effect) -> Annotation 
unliftTuple (a,b) = ATuple [a,b] 


-- | Collect all region variables in an annotation
collect :: Bound -> Annotation -> Constr
collect (Nat 0) _     = M.empty
collect _ AUnit       = M.empty
collect _ (ABot    _) = M.empty 
collect n (AVar    a) = M.singleton (AnnVar a) n 
collect n (AReg    a) = M.singleton (Region a) n 
collect n (AProj i a) = M.mapKeys (CnProj i) $ collect n a
collect n (ATuple ps) = foldr constrAdd M.empty $ map (collect n) ps
collect _ a = rsError $ "collect: Collect of non region annotation: " ++ show a

-- | Is annotation a constraint set?
isConstr :: Annotation -> Bool
isConstr (AConstr _) = True
isConstr _           = False

isTop :: Annotation -> Bool
isTop (ATop _ _) = True
isTop _ = False

isBot :: Annotation -> Bool
isBot (ABot _) = True
isBot _ = False


-- | Convert a constraint index to an annotation
constrIdxToAnn :: ConstrIdx -> Annotation 
constrIdxToAnn (Region r)   = AReg r
constrIdxToAnn (AnnVar a)   = AVar a
constrIdxToAnn (CnProj i c) = AProj i $ constrIdxToAnn c


-- | Clean local regions from the annotation
annRemLocalRegs :: Annotation -> Annotation
annRemLocalRegs = foldAnnAlg cleanAlg
  where cleanAlg = idAnnAlg {
    aMinus  = \_ a _ -> a,
    aReg    = \_ r   -> if r == RegionGlobal then AReg RegionGlobal else ABot SortMonoRegion,
    aConstr = \_     -> AConstr . constrRemLocalRegs,
    aTop    = \_ s   -> ATop s . constrRemLocalRegs
  }
