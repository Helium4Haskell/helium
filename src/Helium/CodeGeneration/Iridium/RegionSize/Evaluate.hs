module Helium.CodeGeneration.Iridium.RegionSize.Evaluate
    ( eval,
    ) where 

import Lvm.Core.Type
import Data.List

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

----------------------------------------------------------------
-- Evalutation
----------------------------------------------------------------

-- | Fully evaluate an expression
eval :: Annotation -> Annotation
eval = foldAnnAlg evalAlg
  where evalAlg = idAnnAlg {
    aAdd   = \_ -> add,
    aMinus = \_ -> minus,
    aJoin  = \_ -> join,
    aApl   = \_ -> application,
    aInstn = \_ -> instantiate,
    aProj  = \_ -> project
  }


-- | Only add when the subannotations are constraints
add :: Annotation -> Annotation -> Annotation
add (AConstr c1) (AConstr c2) = AConstr $ constrAdd c1 c2
-- Empty constraint set? Then ann, otherwise sort
add (AConstr c1) ann | constrBot == c1 = ann
                     | otherwise = AAdd (AConstr c1) ann
add ann (AConstr c2) | constrBot == c2 = ann
                     | otherwise = AAdd (AConstr c2) ann
-- Two non-constraint sets, sort
add c1 c2 = addSort $ collect (AAdd c1 c2)
  where collect (AAdd c3 c4) = collect c3 ++ collect c4 
        collect ann = [ann]
        addSort = operatorSort AAdd constrAdd


-- | Minus of constraint
minus :: Annotation -> RegionVar -> Annotation
minus (AConstr c) r = AConstr $ constrRem (Region r) c
minus a r = AMinus a r


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
join (AQuant a  ) (AQuant b  ) = AQuant   $ AJoin a b
join (AInstn a t) (AInstn b _) = AInstn (AJoin a b) t
-- Collect and sort
join c1 c2 = joinSort $ collect (AJoin c1 c2)
  where collect (AJoin c3 c4) = collect c3 ++ collect c4 
        collect ann = [ann]
        joinSort = operatorSort AJoin constrJoin


-- | Annotation application
application :: Annotation -> Annotation -> Annotation
application (ALam s f) x | sortIsAnnotation s = eval $ annStrengthen $ foldAnnAlg subsAnnAlg f
                         | sortIsRegion     s = eval $ annStrengthen $ foldAnnAlg subsRegAlg f
                         | otherwise = rsError "Sort is neither region or annotation!?"
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \d idx -> if d == idx 
                           then annWeaken d x -- Weaken indexes
                           else AVar idx
        }
        -- | Substitute a region variable for a region
        subsRegAlg = idAnnAlg {
          aConstr = \d c -> AConstr $ regVarSubst x d c
        }
application f x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: Annotation -> Type -> Annotation
instantiate (AQuant anno) ty = eval $ foldAnnAlg annInstAlg anno
  where annInstAlg = idAnnAlg {
    aLam   = \d s a -> ALam (sortSubstitute d ty s) a,
    aFix   = \d s a -> AFix (sortSubstitute d ty s) a
  } 
instantiate a t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: Int -> Annotation -> Annotation 
project idx (ATuple as) | length as > idx = as !! idx
                        | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as)
project idx t = AProj idx t 


----------------------------------------------------------------
-- Evalutation utilities
----------------------------------------------------------------

-- | Ordering of binary operator operands, compute all computable operators
operatorSort :: (Annotation -> Annotation -> Annotation)
             -> (Constr -> Constr -> Constr)
             -> [Annotation] 
             -> Annotation
operatorSort op evalF xs = foldl op constr $ sort other 
  where (constrs, other) = partition isConstr xs
        constr = AConstr $ foldr (\(AConstr a) -> evalF a) constrBot constrs
