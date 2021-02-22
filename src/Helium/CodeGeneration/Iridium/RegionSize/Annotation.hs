module Helium.CodeGeneration.Iridium.RegionSize.Annotation
  ( Annotation(..), 
    AnnAlg(..), foldAnnAlg, foldAnnAlgN, idAnnAlg,
    annWeaken, annStrengthen,
    regVarSubst
  ) where

import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Type

import Data.List
import qualified Data.Map as M
import Lvm.Core.Type

----------------------------------------------------------------
-- Annotation data type
----------------------------------------------------------------

data Annotation = 
      AVar    Int                   -- ^ De Bruijn index Variable
    | AReg    Int                   -- ^ Region
    | ALam    Sort       Annotation -- ^ Annotation lambda
    | AApl    Annotation Annotation -- ^ Application
    | AConstr Constr                -- ^ Constraint set
    | AUnit                         -- ^ Unit annotation
    | ATuple  [Annotation]          -- ^ Unit tuple
    | AProj   Int        Annotation -- ^ Projection
    | AAdd    Annotation Annotation -- ^ Annotation addition
    | AJoin   Annotation Annotation -- ^ Annotation join
    | AQuant  Quantor    Annotation
    | AInstn  Annotation Type
    | ATop    
    | ABot    
    | AFix    Sort       Annotation
  deriving (Eq)

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

-- | TODO: Improve readability for types and quantors
instance Show Annotation where
    show (AVar   idx) = "v$" ++ show idx
    show (AReg   idx) = "r$" ++ show idx
    show (ALam   s a) = "(\\ψ:"++ show s ++"." ++ show a ++ ")"
    show (AApl   a b) = show a ++ "<" ++ show b ++ ">"
    show (AUnit     ) = "()"
    show (ATuple as ) = "(" ++ (intercalate "," $ map show as) ++ ")"
    show (AProj  i a) = "π_" ++ show i ++ "[" ++ show a ++ "]"
    show (AAdd   a b) = show a ++ " ⊕  " ++ show b
    show (AJoin  a b) = show a ++ " ⊔  " ++ show b
    show (AQuant _ a) = "(forall α." ++ show a ++ ")"
    show (AInstn a _) = show a ++ "{" ++ "tau" ++ "}"
    show (ATop      ) = "T"
    show (ABot      ) = "⊥"
    show (AFix   s a) = "fix " ++ show s ++ ". " ++ show a 
    show (AConstr  c) = "{" ++ (intercalate ", " $ map (\(x, b) -> show x ++ " ↦  " ++ show b) $ M.toList c) ++ "}" 

----------------------------------------------------------------
-- Annotation algebra
----------------------------------------------------------------

type Depth = Int

data AnnAlg a = 
  AnnAlg {
    aVar    :: Depth -> Int -> a,         
    aReg    :: Depth -> Int -> a,         
    aLam    :: Depth -> Sort -> a -> a,
    aApl    :: Depth -> a -> a -> a,
    aConstr :: Depth -> Constr -> a,    
    aUnit   :: Depth -> a,
    aTuple  :: Depth -> [a] -> a,
    aProj   :: Depth -> Int -> a -> a,
    aAdd    :: Depth -> a -> a -> a,
    aJoin   :: Depth -> a -> a -> a,
    aQuant  :: Depth -> Quantor -> a -> a,
    aInstn  :: Depth -> a -> Type -> a,
    aTop    :: Depth -> a,
    aBot    :: Depth -> a,
    aFix    :: Depth -> Sort -> a -> a
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
  aJoin   = \_ -> AJoin  ,
  aQuant  = \_ -> AQuant ,
  aInstn  = \_ -> AInstn ,
  aTop    = \_ -> ATop   ,
  aBot    = \_ -> ABot   ,
  aFix    = \_ -> AFix   
}

foldAnnAlg :: AnnAlg a -> Annotation -> a
foldAnnAlg = foldAnnAlgN 1

foldAnnAlgN :: Int -> AnnAlg a -> Annotation -> a
foldAnnAlgN n alg ann = go n ann
  where go d (AVar   idx) = aVar    alg d idx
        go d (AReg   idx) = aReg    alg d idx
        go d (ALam   s a) = aLam    alg d s $ go (d + 1) a
        go d (AApl   a b) = aApl    alg d (go d a) (go d b)
        go d (AUnit     ) = aUnit   alg d 
        go d (ATuple as ) = aTuple  alg d (map (go d) as) 
        go d (AProj  i a) = aProj   alg d i (go d a) 
        go d (AAdd   a b) = aAdd    alg d (go d a) (go d b)
        go d (AJoin  a b) = aJoin   alg d (go d a) (go d b)
        go d (AQuant q a) = aQuant  alg d q $ go (d + 1) a 
        go d (AInstn a t) = aInstn  alg d (go d a) t
        go d (ATop      ) = aTop    alg d 
        go d (ABot      ) = aBot    alg d 
        go d (AFix   s a) = aFix    alg d s (go d a)
        go d (AConstr  c) = aConstr alg d c

----------------------------------------------------------------
-- De Bruijn generic re-indexing 
----------------------------------------------------------------

-- | Don't route subdD
annReIndex :: (Depth -> Int -> Int) -- ^ Reindex function (depth in body to idx to idx)
           -> Annotation -> Annotation
annReIndex f = foldAnnAlg reIdxAlg
  where reIdxAlg = idAnnAlg {
    aLam    = \d s a -> ALam (sortReIndex f d s) a,
    aFix    = \d s a -> AFix (sortReIndex f d s) a,
    aConstr = \d c   -> AConstr (constrReIndex f d c), 
    aVar    = \d idx -> AVar (f d idx)
  }

-- | Re-index the debruin indices of a sort
sortReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
            -> Int -- ^ Depth in annotation
            -> Sort -> Sort
sortReIndex f annD = foldSortAlgN annD reIdxAlg
  where reIdxAlg = idSortAlg {
    sortPolyRegion = \d idx ts -> SortPolyRegion (f d idx) ts,
    sortPolySort   = \d idx ts -> SortPolySort   (f d idx) ts
  }

-- | Re-index the debruijn indices of a cosntraint set 
constrReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
              -> Int -- ^ Depth of constraint set in annotation
              -> Constr -> Constr
constrReIndex f annD = M.mapKeys keyReIndex
  where keyReIndex (ReV idx) = ReV $ f annD idx
        keyReIndex (Reg idx) = Reg idx

----------------------------------------------------------------
-- De Bruijn reindexing implementations
----------------------------------------------------------------

-- | Weaken all unbound variables by the substitution depth
annWeaken :: Depth -- ^ Depth of the substitution
          -> Annotation -> Annotation
annWeaken subD = annReIndex idxReIndex 
  where idxReIndex d idx = if idx >= d  -- If idx >= d: var points outside of applicated term
                           then idx + subD -- Reindex
                           else idx 

-- | Strengthen all unbound indexes by 1
annStrengthen :: Annotation -> Annotation
annStrengthen = annReIndex strgthIdx
  where strgthIdx d idx = if idx > d 
                          then idx - 1 
                          else idx

----------------------------------------------------------------
-- Annotation utilities
----------------------------------------------------------------

-- | Initialize region variables in a constraint set
regVarSubst :: Annotation -> RegVar -> Constr -> Constr 
regVarSubst ann r c = constrInst inst r c
  where n    = constrIdx (ReV r) c
        inst = collect n ann

-- | Collect all region variables in tuple
collect :: Int -> Annotation -> Constr
collect 0 _           = M.empty
collect _ AUnit       = M.empty
collect n (AVar    a) = M.singleton (ReV a) n
collect n (AReg    a) = M.singleton (Reg a) n
collect n (ATuple ps) = foldr constrAdd M.empty $ map (collect n) ps
collect _ _ = rsError "Collect of non region annotation"
