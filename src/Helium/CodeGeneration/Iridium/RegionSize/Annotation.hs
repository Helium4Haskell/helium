{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.RegionSize.Annotation
  ( Annotation(..), pattern AUnit,
    AnnAlg(..), foldAnnAlg, foldAnnAlgN, idAnnAlg,
    collect,
    annWeaken, annStrengthen,
    isConstr, constrIdxToAnn,
    annRemLocalRegs
  ) where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type

import qualified Data.Map as M
import Data.List
import Lvm.Core.Type

----------------------------------------------------------------
-- Annotation data type
----------------------------------------------------------------

data Annotation = 
      AVar    Int                   -- ^ De Bruijn i7ndex Variable
    | AReg    RegionVar             -- ^ Region
    | ALam    Sort       Annotation -- ^ Annotation lambda
    | AApl    Annotation Annotation -- ^ Application
    | AConstr Constr                -- ^ Constraint set
    | ATuple  [Annotation]          -- ^ Unit tuple
    | AProj   Int        Annotation -- ^ Projection
    | AAdd    Annotation Annotation -- ^ Constraint set addition
    | AMinus  Annotation RegionVar  -- ^ Constraint set minus
    | AJoin   Annotation Annotation -- ^ Annotation join
    | AQuant  Annotation
    | AInstn  Annotation Type
    | ATop    Sort
    | ABot    Sort
    | AFix    Sort     [Annotation] -- ^ Fix point has a list of data (Turns into tuple after eval)
  deriving (Eq, Ord)

-- | AUnit is a 0-tuple, a patern disallows them from co-existing
pattern AUnit = ATuple []

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Show Annotation where
    show = foldAnnAlg showAlg
      where showAlg = AnnAlg {
        aVar    = \d idx -> annVarName (d - idx),
        aReg    = \_ idx -> show idx,
        aLam    = \d s a -> "(λ"++ annVarName (d+1) ++":"++ showSort d s ++ ".\n" ++ indent a ++ ")",
        aApl    = \_ a b -> a ++ "< " ++ b ++ " >",
        aUnit   = \_     -> "()",
        aTuple  = \_ as  -> "(" ++ intercalate (if noTupleBreak (as !! 0) then "," else "\n,") as ++ ")",
        aProj   = \_ i a -> "π_" ++ show i ++ "[" ++ a ++ "]",
        aAdd    = \_ a b -> "(" ++ a ++ " ⊕  " ++ b ++ ")",
        aMinus  = \_ a r -> "(" ++ a ++ " \\ " ++ show r ++ ")",
        aJoin   = \_ a b -> "(" ++ a ++ " ⊔  " ++ b ++ ")",
        aQuant  = \d a   -> "(∀ " ++ typeVarName (d+1) ++ "." ++ a ++ ")",
        aInstn  = \d a t -> a ++ " {" ++ showTypeN d t ++ "}",
        aTop    = \_ _   -> "T",
        aBot    = \_ _   -> "⊥",
        aFix    = \d s a -> "fix " ++ annVarName (d+1) ++ " : " ++ showSort d s 
                                   ++ ".\n[" ++ (indent $ intercalate ",\n" a) ++ "]",
        aConstr = \d c   -> constrShow d c
      }

----------------------------------------------------------------
-- Annotation algebra
----------------------------------------------------------------

type Depth = Int

data AnnAlg a = 
  AnnAlg {
    aVar    :: Depth -> Int -> a,         
    aReg    :: Depth -> RegionVar -> a,         
    aLam    :: Depth -> Sort -> a -> a,
    aApl    :: Depth -> a -> a -> a,
    aConstr :: Depth -> Constr -> a,    
    aUnit   :: Depth -> a,
    aTuple  :: Depth -> [a] -> a,
    aProj   :: Depth -> Int -> a -> a,
    aAdd    :: Depth -> a -> a -> a,
    aMinus  :: Depth -> a -> RegionVar -> a,
    aJoin   :: Depth -> a -> a -> a,
    aQuant  :: Depth -> a -> a,
    aInstn  :: Depth -> a -> Type -> a,
    aTop    :: Depth -> Sort -> a,
    aBot    :: Depth -> Sort -> a,
    aFix    :: Depth -> Sort -> [a] -> a
  }

idAnnAlg :: AnnAlg Annotation
idAnnAlg = AnnAlg {
  aVar    = \_ -> AVar   ,
  aReg    = \_ -> AReg   ,
  aLam    = \_ -> ALam   ,
  aApl    = \_ -> AApl   ,
  aConstr = \_ -> AConstr,
  aUnit   = \_ -> AUnit  ,
  aTuple  = \_ -> ATuple ,
  aProj   = \_ -> AProj  ,
  aAdd    = \_ -> AAdd   ,
  aMinus  = \_ -> AMinus ,
  aJoin   = \_ -> AJoin  ,
  aQuant  = \_ -> AQuant ,
  aInstn  = \_ -> AInstn ,
  aTop    = \_ -> ATop   ,
  aBot    = \_ -> ABot   ,
  aFix    = \_ -> AFix   
}

foldAnnAlg :: AnnAlg a -> Annotation -> a
foldAnnAlg = foldAnnAlgN (-1)

foldAnnAlgN :: Int -> AnnAlg a -> Annotation -> a
foldAnnAlgN n alg ann = go n ann
  where go d (AVar   idx) = aVar    alg d idx
        go d (AReg   idx) = aReg    alg d idx
        go d (ALam   s a) = aLam    alg d s $ go (d + 1) a
        go d (AApl   a b) = aApl    alg d (go d a) (go d b)
        go d (AUnit     ) = aUnit   alg d 
        go d (ATuple as ) = aTuple  alg d (go d <$> as) 
        go d (AProj  i a) = aProj   alg d i (go d a) 
        go d (AAdd   a b) = aAdd    alg d (go d a) (go d b)
        go d (AMinus a r) = aMinus  alg d (go d a) r
        go d (AJoin  a b) = aJoin   alg d (go d a) (go d b)
        go d (AQuant a  ) = aQuant  alg d $ go (d + 1) a 
        go d (AInstn a t) = aInstn  alg d (go d a) t
        go d (ATop   s  ) = aTop    alg d s
        go d (ABot   s  ) = aBot    alg d s
        go d (AFix   s a) = aFix    alg d s (go (d+1) <$> a)
        go d (AConstr  c) = aConstr alg d c

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------

-- | Re-index the debruin indices of an annotation
annReIndex :: (Depth -> Int -> Int) -- ^ Reindex function (depth in body to idx to idx)
           -> Annotation -> Annotation
annReIndex f = foldAnnAlg reIdxAlg
  where reIdxAlg = idAnnAlg {
    aLam    = \d s a -> ALam (sortReIndex f d s) a,
    aFix    = \d s a -> AFix (sortReIndex f d s) a,
    aConstr = \d c   -> AConstr (constrReIndex f d c), 
    aVar    = \d idx -> AVar (f d idx)
  }

-- | Increase all unbound variables by the substitution depth
annWeaken :: Depth -- ^ Depth of the substitution
          -> Annotation -> Annotation
annWeaken subD = annReIndex $ weakenIdx subD 

-- | Decrease all unbound indexes by 1
annStrengthen :: Annotation -> Annotation
annStrengthen = annReIndex strengthenIdx

----------------------------------------------------------------
-- Annotation utilities
----------------------------------------------------------------

-- | Collect all region variables in an annotation
collect :: Bound -> Annotation -> Constr
collect (Nat 0) _     = M.empty
collect _ AUnit       = M.empty
collect n (ABot    _) = M.empty 
collect n (AVar    a) = M.singleton (AnnVar a) n 
collect n (AReg    a) = M.singleton (Region a) n 
collect n (AProj i a) = M.mapKeys (CnProj i) $ collect n a
collect n (ATuple ps) = foldr constrAdd M.empty $ map (collect n) ps
collect _ _ = rsError "collect: Collect of non region annotation"

-- | Is annotation a constraint set?
isConstr :: Annotation -> Bool
isConstr (AConstr _) = True
isConstr _           = False

-- | Check if an annotation is a region
annIsRegion :: Annotation -> Bool
annIsRegion (AReg _)     = True
annIsRegion AUnit        = False
annIsRegion (ATuple ts)  = annIsRegion $ ts !! 0
annIsRegion (AProj _ ts) = annIsRegion ts
annIsRegion _            = False

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
    aReg    = \_ r   -> if r == RegionGlobal then AReg r else ABot SortMonoRegion,
    aConstr = \_     -> AConstr . constrRemLocalRegs
  }
