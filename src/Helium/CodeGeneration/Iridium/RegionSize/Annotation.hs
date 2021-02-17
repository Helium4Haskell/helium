module Helium.CodeGeneration.Iridium.RegionSize.Annotation
where

import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Sort

import Data.List
import qualified Data.Map as M
import Lvm.Core.Type

----------------------------------------------------------------
-- Annotation data type
----------------------------------------------------------------

data Annotation = 
      AVar    Int                   -- ^ De Bruijn index Variable
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

----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

-- | TODO: Improve readability for types and quantors
instance Show Annotation where
    show (AVar   idx) = "v$" ++ show idx
    show (ALam   s a) = "(\\ψ:"++ show s ++"." ++ show a ++ ")"
    show (AApl   a b) = show a ++ " " ++ show b
    show (AUnit     ) = "()"
    show (ATuple as ) = "(" ++ (intercalate "," $ map show as) ++ ")"
    show (AProj  i a) = "π_" ++ show i ++ "[" ++ show a ++ "]"
    show (AAdd   a b) = show a ++ " ⊕ " ++ show b
    show (AJoin  a b) = show a ++ " ⊔ " ++ show b
    show (AQuant _ a) = "(forall α." ++ show a ++ ")"
    show (AInstn a _) = show a ++ "{" ++ "tau" ++ "}"
    show (ATop      ) = "T"
    show (ABot      ) = "⊥"
    show (AFix   s a) = "fix " ++ show s ++ ". " ++ show a 
    show (AConstr  c) = "{" ++ (intercalate ", " $ map (\(x, b) -> "p_" ++ show x ++ " ↦  " ++ show b) $ M.toList c) ++ "}" 

----------------------------------------------------------------
-- Annotation algebra
----------------------------------------------------------------

type Depth = Int

data AnnAlg a = 
  AnnAlg {
    aVar    :: Depth -> Int -> a,         
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

execAnnAlg :: AnnAlg a -> Annotation -> a
execAnnAlg alg ann = go 0 ann
  where go d (AVar   idx) = aVar    alg d idx
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
-- Annotation utilities
----------------------------------------------------------------

-- | TODO: ID function as annotation
annotationId :: Annotation
annotationId = AQuant undefined (ALam (SortConstr) (AVar 0)) 

annReIndex :: Annotation
annReIndex = undefined -- TODO: reindexing