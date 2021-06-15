{-# LANGUAGE PatternSynonyms #-}

module Helium.CodeGeneration.Iridium.RegionSize.Annotation
  ( Annotation(..), Effect, pattern AUnit, annShow, annShow',
    AnnAlg(..), foldAnnAlg, foldAnnAlgN, 
    foldAnnAlgLams, foldAnnAlgLamsN,
    foldAnnAlgQuants, foldAnnAlgQuantsN,
    idAnnAlg
  ) where

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Data.List
import Lvm.Core.Type

----------------------------------------------------------------
-- Annotation data type
----------------------------------------------------------------

data Annotation = 
      AVar    Int                     -- ^ De Bruijn index Variable
    | AReg    RegionVar               -- ^ Region
    | ALam    Sort       Annotation   -- ^ Annotation lambda
    | AApl    Annotation Annotation   -- ^ Application
    | AConstr Constr                  -- ^ Constraint set
    | ATuple  [Annotation]            -- ^ Unit tuple
    | AProj   Int        Annotation   -- ^ Projection
    | AAdd    Annotation Annotation   -- ^ Constraint set addition
    -- | AMinus  Annotation RegionVar    -- ^ Constraint set minus
    | AJoin   Annotation Annotation   -- ^ Annotation join
    | AQuant  Annotation              -- ^ Quantification
    | AInstn  Annotation Type         -- ^ Insantiation of quantification
    | ATop    Sort       Constr       -- ^ Has a constraint set, all bounds should be infty
    | ABot    Sort  
    | AFix    [Sort]     [Annotation] -- ^ Fix point has a list of (possibly mutally recursive) annotations
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
annShow = annShow' $ (-1,-1)

annShow' :: (Int,Int) -> Annotation -> String     
annShow' n = foldAnnAlgN n showAlg 
     where showAlg = AnnAlg { 
        aVar    = \(lD,_ ) idx -> annVarName (lD - idx), 
        aReg    = \(_ ,_ ) reg -> show reg, 
        aLam    = \(lD,qD) s a -> "(λ"++ annVarName (lD+1) ++":"++ showSort qD s ++ ".\n" ++ indent "  " a ++ ")", 
        aApl    = \(_, _ ) a b -> a ++ "<" ++ indent " "  b ++ " >", 
        aUnit   = \(_ ,_ )     -> "TUP()", 
        aTuple  = \(_ ,_ ) as  -> "TUP(" ++ intercalate (if noTupleBreak (as !! 0) then "," else "\n,") as ++ ")", 
        aProj   = \(_ ,_ ) i a -> "π_" ++ show i ++ "[" ++ a ++ "]", 
        aAdd    = \(_ ,_ ) a b -> "(" ++ a ++ " ⊕  " ++ b ++ ")", 
        -- aMinus  = \(_ ,_ ) a r -> "(" ++ a ++ " \\ " ++ show r ++ ")", 
        aJoin   = \(_ ,_ ) a b -> "(" ++ a ++ " ⊔  " ++ b ++ ")", 
        aQuant  = \(_ ,qD) a   -> "(∀ " ++ typeVarName (qD+1) ++ "." ++ a ++ ")", 
        aInstn  = \(_ ,qD) a t -> a ++ " {" ++ rsShowType t ++ "}", 
        aTop    = \(lD,qD) s c -> "T[" ++ constrShow lD c ++ ":" ++ showSort qD s ++ "]", 
        aBot    = \(_ ,qD) s   -> "⊥[" ++ showSort qD s ++ "]", 
        aFix    = \(lD,qD) s a -> "fix " ++ annVarName (lD+1) ++ " : " ++ showSort qD (SortTuple s)  
                                         ++ ".\n[" ++ (intercalate ",\n" $ mapWithIndex (\i str -> show i ++ ": " ++ str) 
                                          $ indent "  " <$> a) ++ "]", 
        aConstr = \(lD,_ ) c   -> constrShow lD c 
      } 

----------------------------------------------------------------
-- Annotation algebra
----------------------------------------------------------------

data AnnAlg b a = 
  AnnAlg {
    aVar    :: b -> Int -> a,         
    aReg    :: b -> RegionVar -> a,         
    aLam    :: b -> Sort -> a -> a,
    aApl    :: b -> a -> a -> a,
    aConstr :: b -> Constr -> a,    
    aUnit   :: b -> a,
    aTuple  :: b -> [a] -> a,
    aProj   :: b -> Int -> a -> a,
    aAdd    :: b -> a -> a -> a,
    -- aMinus  :: b -> a -> RegionVar -> a,
    aJoin   :: b -> a -> a -> a,
    aQuant  :: b -> a -> a,
    aInstn  :: b -> a -> Type -> a,
    aTop    :: b -> Sort -> Constr -> a,
    aBot    :: b -> Sort -> a,
    aFix    :: b -> [Sort] -> [a] -> a
  }

idAnnAlg :: AnnAlg a Annotation
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
  -- aMinus  = \_ -> AMinus ,
  aJoin   = \_ -> AJoin  ,
  aQuant  = \_ -> AQuant ,
  aInstn  = \_ -> AInstn ,
  aTop    = \_ -> ATop   ,
  aBot    = \_ -> ABot   ,
  aFix    = \_ -> AFix   
}



-- | Start folding from default depth (-1)
foldAnnAlg :: AnnAlg (Int,Int) a -> Annotation -> a
foldAnnAlg = foldAnnAlgN (-1,-1)

-- | Increase depth at lambdas and quantifications
foldAnnAlgN :: (Int,Int) -> AnnAlg (Int,Int) a -> Annotation -> a
foldAnnAlgN = foldAnnAlgN' (\(a,b) -> (a+1,b)) (\(a,b) -> (a,b+1))



-- | Start folding from default depth (-1)
foldAnnAlgLams :: AnnAlg Int a -> Annotation -> a
foldAnnAlgLams = foldAnnAlgLamsN (-1)

-- | Increase depth only at lambdas (thus also fixpoints)
foldAnnAlgLamsN :: Int -> AnnAlg Int a -> Annotation -> a
foldAnnAlgLamsN = foldAnnAlgN' (+1) (+0)



-- | Start folding from default depth (-1)
foldAnnAlgQuants :: AnnAlg Int a -> Annotation -> a
foldAnnAlgQuants = foldAnnAlgQuantsN (-1)

-- | Increase depth only at lambdas (thus also fixpoints)
foldAnnAlgQuantsN :: Int -> AnnAlg Int a -> Annotation -> a
foldAnnAlgQuantsN = foldAnnAlgN' (+0) (+1)



-- | Generic fold over annotations 
foldAnnAlgN' :: (a -> a) -- ^ Increment function for lams
             -> (a -> a) -- ^ Increment function for quants
             -> a -> AnnAlg a b -> Annotation -> b
foldAnnAlgN' incrLam incrQuant n alg ann = go n ann
  where go d (AVar   idx) = aVar    alg d idx
        go d (AReg   idx) = aReg    alg d idx
        go d (ALam   s a) = aLam    alg d s $ go (incrLam d) a
        go d (AApl   a b) = aApl    alg d (go d a) (go d b)
        go d (AUnit     ) = aUnit   alg d 
        go d (ATuple as ) = aTuple  alg d (go d <$> as) 
        go d (AProj  i a) = aProj   alg d i (go d a) 
        go d (AAdd   a b) = aAdd    alg d (go d a) (go d b)
        -- go d (AMinus a r) = aMinus  alg d (go d a) r
        go d (AJoin  a b) = aJoin   alg d (go d a) (go d b)
        go d (AQuant a  ) = aQuant  alg d $ go (incrQuant d) a 
        go d (AInstn a t) = aInstn  alg d (go d a) t
        go d (ATop   s v) = aTop    alg d s v
        go d (ABot   s  ) = aBot    alg d s
        go d (AFix   s a) = aFix    alg d s (go (incrLam d) <$> a)
        go d (AConstr  c) = aConstr alg d c