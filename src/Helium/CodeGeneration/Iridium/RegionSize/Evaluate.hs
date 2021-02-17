module Helium.CodeGeneration.Iridium.RegionSize.Evaluate
    ( eval
    ) where 

import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

----------------------------------------------------------------
-- Evalutation
----------------------------------------------------------------

-- | Fully evaluate an expression
eval :: Annotation -> Annotation
eval = execAnnAlg evalAlg
  where evalAlg = idAnnAlg {
    aAdd   = \_ -> add,
    aJoin  = \_ -> join,
    aApl   = \_ -> application,
    aInstn = \_ -> instantiate,
    aProj  = \_ -> project
  }


-- | Only add when the subannotations are constraints
add :: Annotation -> Annotation -> Annotation
add (AConstr c1) (AConstr c2) = AConstr $ constrAdd c1 c2
add c1 c2 = AAdd c1 c2 -- TODO: Addition of other sorts?


-- | Join of annotations
join :: Annotation -> Annotation -> Annotation
-- Join with constants
join _ AUnit = AUnit
join AUnit _ = AUnit 
join ABot  a = a 
join a  ABot = a 
join ATop  _ = ATop 
join _  ATop = ATop
-- Constraint set join
join (AConstr c1) (AConstr c2) = AConstr $ constrJoin c1 c2
-- Join-simplicitation
join (ALam   s a) (ALam   _ b) = ALam   s $ AJoin a b
join (AApl   s a) (AApl   _ b) = AApl   s $ AJoin a b
join (AQuant q a) (AQuant _ b) = AQuant q $ AJoin a b
join (AInstn a t) (AInstn b _) = AInstn (AJoin a b) t
join _ _ = error "No join" -- TODO: Return Join



-- | Only project if subannotation has been evaluated to a tuple
project :: Int -> Annotation -> Annotation 
project idx (ATuple as) | length as > idx = as !! idx
                        | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as)
project _ t = t 


-- | TODO: Application
application :: Annotation -> Annotation -> Annotation
application (ALam s f) x | sortIsAnnotation s = execAnnAlg subsAnnAlg f
                         | sortIsRegion     s = execAnnAlg subsRegAlg f
                         | otherwise = rsError "Sort is neither region or annotation!?" -- TODO: Remove error? should never occur
  where
    -- | Substitute a variable for an annotation
    subsAnnAlg :: AnnAlg Annotation
    subsAnnAlg = idAnnAlg {
      aVar = \d idx -> if d == idx then x else AVar idx
    }
    -- | Substitute a region variable for a region
    subsRegAlg :: AnnAlg Annotation
    subsRegAlg = idAnnAlg -- TODO
application f x = AApl f x




-- | Instantiate a type if it starts with a quantification 
instantiate :: Annotation -> Type -> Annotation
instantiate (AQuant quant anno) ty = execAnnAlg annInstAlg anno
  where annInstAlg = idAnnAlg {
    aLam   = \_ s a -> ALam (sortInstantiate quant ty s) a,
    aFix   = \_ s a -> AFix (sortInstantiate quant ty s) a
  } 
instantiate a t = AInstn a t






