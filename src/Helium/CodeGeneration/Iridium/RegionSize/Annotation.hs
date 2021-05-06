{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.RegionSize.Annotation
  ( Annotation(..), Effect, pattern AUnit, annShow, annShow',
    AnnAlg(..), foldAnnAlg, foldAnnAlgN, foldAnnAlgLams, idAnnAlg
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
      AVar    Int                     -- ^ De Bruijn i7ndex Variable
    | AReg    RegionVar               -- ^ Region
    | ALam    Sort       Annotation   -- ^ Annotation lambda
    | AApl    Annotation Annotation   -- ^ Application
    | AConstr Constr                  -- ^ Constraint set
    | ATuple  [Annotation]            -- ^ Unit tuple
    | AProj   Int        Annotation   -- ^ Projection
    | AAdd    Annotation Annotation   -- ^ Constraint set addition
    | AMinus  Annotation RegionVar    -- ^ Constraint set minus
    | AJoin   Annotation Annotation   -- ^ Annotation join
    | AQuant  Annotation              -- ^ Quantification
    | AInstn  Annotation Type         -- ^ Insantiation of quantification
    | ATop    Sort       Constr       -- ^ Has a constraint set, all bounds should be infty
    | ABot    Sort  
    | AFix    Sort       [Annotation] -- ^ Fix point has a list of (possibly mutally recursive) annotations
  deriving (Eq, Ord)

-- | The effect is an annotation, but always of sort C
type Effect = Annotation

-- | AUnit is a 0-tuple, a patern disallows them from co-existing
pattern AUnit :: Annotation
pattern AUnit = ATuple []

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

instance Show Annotation where
  show = cleanTUP . annShow


annShow :: Annotation -> String    
annShow = annShow' $ -1

annShow' :: Int -> Annotation -> String    
annShow' n = foldAnnAlgN n showAlg
     where showAlg = AnnAlg {
        aVar    = \d idx -> annVarName (d - idx),
        aReg    = \_ idx -> show idx,
        aLam    = \d s a -> "(λ"++ annVarName (d+1) ++":"++ showSort d s ++ ".\n" ++ indent "  " a ++ ")",
        aApl    = \_ a b -> a ++ "<" ++ indent " "  b ++ " >",
        aUnit   = \_     -> "TUP()",
        aTuple  = \_ as  -> "TUP(" ++ intercalate (if noTupleBreak (as !! 0) then "," else "\n,") as ++ ")",
        aProj   = \_ i a -> "π_" ++ show i ++ "[" ++ a ++ "]",
        aAdd    = \_ a b -> "(" ++ a ++ " ⊕  " ++ b ++ ")",
        aMinus  = \_ a r -> "(" ++ a ++ " \\ " ++ show r ++ ")",
        aJoin   = \_ a b -> "(" ++ a ++ " ⊔  " ++ b ++ ")",
        aQuant  = \d a   -> "(∀ " ++ typeVarName (d+1) ++ "." ++ a ++ ")",
        aInstn  = \d a t -> a ++ " {" ++ showTypeN d t ++ "}",
        aTop    = \d s c -> "T[" ++ (constrShow d c) ++ ":" ++ showSort d s ++ "]",
        aBot    = \d s   -> "⊥[" ++ showSort d s ++ "]",
        aFix    = \d s a -> "fix " ++ annVarName (d+1) ++ " : " ++ showSort d s 
                                   ++ ".\n[" ++ (intercalate ",\n" $ mapWithIndex (\i str -> show i ++ ": " ++ str) $ indent "  " <$> a) ++ "]",
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
    aTop    :: Depth -> Sort -> Constr -> a,
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

-- | Start folding from default depth (-1)
foldAnnAlg :: AnnAlg a -> Annotation -> a
foldAnnAlg = foldAnnAlgN (-1)

-- | Increase depth at lambdas and quantifications
foldAnnAlgN :: Int -> AnnAlg a -> Annotation -> a
foldAnnAlgN = foldAnnAlgN' (+1) (+1)

-- | Start folding from default depth (-1)
foldAnnAlgLams :: AnnAlg a -> Annotation -> a
foldAnnAlgLams = foldAnnAlgLamsN (-1)

-- | Increase depth only at lambdas (thus also fixpoints)
foldAnnAlgLamsN :: Int -> AnnAlg a -> Annotation -> a
foldAnnAlgLamsN = foldAnnAlgN' (+1) (+0)


-- | Generic fold over annotations 
foldAnnAlgN' :: (Int -> Int) -- ^ Increment function for lams
             -> (Int -> Int) -- ^ Increment function for quants
             -> Int -> AnnAlg a -> Annotation -> a
foldAnnAlgN' incrLam incrQuant n alg ann = go n ann
  where go d (AVar   idx) = aVar    alg d idx
        go d (AReg   idx) = aReg    alg d idx
        go d (ALam   s a) = aLam    alg d s $ go (incrLam d) a
        go d (AApl   a b) = aApl    alg d (go d a) (go d b)
        go d (AUnit     ) = aUnit   alg d 
        go d (ATuple as ) = aTuple  alg d (go d <$> as) 
        go d (AProj  i a) = aProj   alg d i (go d a) 
        go d (AAdd   a b) = aAdd    alg d (go d a) (go d b)
        go d (AMinus a r) = aMinus  alg d (go d a) r
        go d (AJoin  a b) = aJoin   alg d (go d a) (go d b)
        go d (AQuant a  ) = aQuant  alg d $ go (incrQuant d) a 
        go d (AInstn a t) = aInstn  alg d (go d a) t
        go d (ATop   s v) = aTop    alg d s v
        go d (ABot   s  ) = aBot    alg d s
        go d (AFix   s a) = aFix    alg d s (go (incrLam d) <$> a)
        go d (AConstr  c) = aConstr alg d c