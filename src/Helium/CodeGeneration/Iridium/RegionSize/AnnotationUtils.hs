module Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
  ( liftTuple, unliftTuple, unsafeUnliftTuple,
    collect, collectEffects,
    annWeaken,
    isConstr, isTop, isBot, constrIdxToAnn,
    annRemLocalRegs, regionVarsToGlobal
  ) where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import qualified Data.Map as M

import GHC.Stack

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------
type Depth = Int

-- | Re-index the debruin indices of an annotation
annReIndex :: (Depth -> Int -> Int) -- ^ Reindex function for annotation vars
           -> (Depth -> Int -> Int) -- ^ Reindex function for type vars
           -> Annotation -> Annotation
annReIndex fA fT = foldAnnAlg reIdxAlg
  where reIdxAlg = idAnnAlg {
    aLam    = \(_ , qD) s a -> ALam (sortReIndex fT qD s) a,
    aFix    = \(_ , qD) s a -> AFix (sortReIndex fT qD <$> s) a,
    aConstr = \(lD, _ ) c   -> AConstr (constrReIndex fA lD c), 
    aTop    = \(lD, qD) s c -> ATop (sortReIndex fT qD s) (constrReIndex fA lD c), 
    aBot    = \(_ , qD) s   -> ABot (sortReIndex fT qD s), 
    aVar    = \(lD, _ ) idx -> AVar (fA lD idx)
  }

-- | Increase all unbound variables by the substitution depth
annWeaken :: Depth -- ^ Lambda depth
          -> Depth -- ^ Quantification depth
          -> Annotation -> Annotation
annWeaken lD qD = annReIndex (weakenIdx lD) (id.const)

----------------------------------------------------------------
-- Annotation utilities
----------------------------------------------------------------

-- | Convert an annotation tuple to a haskell tuple
liftTuple :: Annotation -> (Annotation, Effect)
liftTuple a = (AProj 0 a, AProj 1 a) 

-- | Convert an annotation tuple to a haskell tuple
unliftTuple :: (Annotation, Effect) -> Annotation 
unliftTuple (a,b) = ATuple [a,b] 

-- | Get an array of annotations from a tuple
unsafeUnliftTuple :: Annotation -> [Annotation]
unsafeUnliftTuple (ATuple as) = as
unsafeUnliftTuple a = rsError $ "unsafeUnliftTuple: Called unsafe unlift tuple on non-tuple: " ++ show a


-- | Collect all region variables in an annotation
collect :: HasCallStack => Bound -> Annotation -> Constr
collect (Nat 0) _     = M.empty
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
    aReg    = \_ r   -> if r == RegionGlobal then AReg RegionGlobal else AReg RegionBottom,
    aConstr = \_     -> AConstr . constrRemLocalRegs,
    aTop    = \_ s   -> ATop s . constrRemLocalRegs
  }

-- | Collect all constraint sets from an annotation
collectEffects :: Annotation -> Constr
collectEffects = foldAnnAlg collectAlg
    where collectAlg = AnnAlg {
        aVar    = \_ _   -> constrBot,
        aReg    = \_ _   -> constrBot,
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> constrAdd a b,
        aConstr = \_ c   -> c,
        aUnit   = \_     -> constrBot,
        aTuple  = \_ as  -> foldr constrAdd constrBot as,
        aProj   = \_ _ a -> a,
        aAdd    = \_ a b -> constrAdd a b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> constrAdd a b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \_ _ c -> c,
        aBot    = \_ _   -> constrBot,
        aFix    = \_ _ a -> foldr constrAdd constrBot a
    }

-- | Create an annotation that assigns all regionvars the global region
regionVarsToGlobal :: RegionVars -> Annotation
regionVarsToGlobal (RegionVarsSingle _) = AReg RegionGlobal
regionVarsToGlobal (RegionVarsTuple rs) = ATuple $ regionVarsToGlobal <$> rs
