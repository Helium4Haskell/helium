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

data AnnAlg a = 
  AnnAlg {
    aVar    :: Int -> a,         
    aLam    :: Sort -> a -> a,
    aApl    :: a -> a -> a,
    aConstr :: Constr -> a,    
    aUnit   :: a,
    aTuple  :: [a] -> a,
    aAdd    :: a -> a -> a,
    aJoin   :: a -> a -> a,
    aQuant  :: Quantor -> a -> a,
    aInstn  :: a -> Type -> a,
    aTop    :: a,
    aBot    :: a,
    aFix    :: Sort -> a -> a
  }

idAnnAlg :: AnnAlg Annotation
idAnnAlg = AnnAlg {
  aVar    = AVar   ,
  aLam    = ALam   ,
  aApl    = AApl   ,
  aConstr = AConstr,
  aUnit   = AUnit  ,
  aTuple  = ATuple ,
  aAdd    = AAdd   ,
  aJoin   = AJoin  ,
  aQuant  = AQuant ,
  aInstn  = AInstn ,
  aTop    = ATop   ,
  aBot    = ABot   ,
  aFix    = AFix   
}

execAnnAlg :: AnnAlg a -> Annotation -> a
execAnnAlg alg ann = go ann
  where go (AVar   idx) = aVar    alg idx
        go (ALam   s a) = aLam    alg s (go a)
        go (AApl   a b) = aApl    alg (go a) (go b)
        go (AUnit     ) = aUnit   alg
        go (ATuple as ) = aTuple  alg $ map go as 
        go (AAdd   a b) = aAdd    alg (go a) (go b)
        go (AJoin  a b) = aJoin   alg (go a) (go b)
        go (AQuant q a) = aQuant  alg q (go a) 
        go (AInstn a t) = aInstn  alg (go a) t
        go (ATop      ) = aTop    alg 
        go (ABot      ) = aBot    alg 
        go (AFix   s a) = aFix    alg s (go a)
        go (AConstr  c) = aConstr alg c

----------------------------------------------------------------
-- Annotation utilities
----------------------------------------------------------------

annotationId :: Annotation
annotationId = AQuant undefined (ALam (SortConstr) (AVar 0)) 

eval :: Annotation -> Annotation
eval = execAnnAlg evalAlg
  where evalAlg = idAnnAlg {
    aAdd   = \a b -> add  (eval a) (eval b),
    aJoin  = \a b -> join (eval a) (eval b),
    aInstn = \a t -> annoInstantiate t (eval a),
    aApl   = undefined -- | TODO: aApl
  }

annoInstantiate :: Type -> Annotation -> Annotation
annoInstantiate t (AQuant quant anno) = execAnnAlg annInstAlg anno
  where annInstAlg = idAnnAlg {
    aLam   = \s a -> ALam (sortInstantiate quant t s) a,
    aFix   = \s a -> AFix (sortInstantiate quant t s) a
  } 
annoInstantiate t a          = AInstn a t

add :: Annotation -> Annotation -> Annotation
add (AConstr c1) (AConstr c2) = AConstr $ constrAdd c1 c2
add _ _ = error "Addition of non-constraint sets" -- TODO: Addition of other annotations

join :: Annotation -> Annotation -> Annotation
join a b = AJoin a b -- TODO: Join

