module Helium.CodeGeneration.Iridium.RegionSize.Evaluate
    ( eval
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
add (ATop s) _ = ATop s
add _ (ATop s) = ATop s
add (AConstr c1) (AConstr c2) = AConstr $ constrAdd c1 c2
-- Empty constraint set? Then ann, otherwise sort
add (AConstr c1) ann | constrBot == c1 = ann
                     | otherwise = AAdd (AConstr c1) ann
add ann (AConstr c2) | constrBot == c2 = ann
                     | otherwise = AAdd (AConstr c2) ann
-- Two non-constraint sets, sort
add c1  c2 = addSort $ aCollect (AAdd c1 c2)
  where aCollect (AAdd c3 c4) = aCollect c3 ++ aCollect c4 
        aCollect ann = [ann]
        addSort = operatorSort AAdd constrAdd


-- | Minus of constraint
minus :: Annotation -> RegionVar -> Annotation
minus (ATop s)    _ = ATop s
minus (AConstr c) r = AConstr $ constrRem (Region r) c
minus a r = AMinus a r


-- | Join of annotations
join :: Annotation -> Annotation -> Annotation
-- Join with constants
join _ AUnit     = AUnit
join AUnit _     = AUnit 
join (ABot _)  a = a 
join a  (ABot _) = a 
join (ATop s)  _ = ATop s
join _  (ATop s) = ATop s
-- Constraint set join
join (AConstr c1) (AConstr c2) = AConstr $ constrJoin c1 c2
-- Join-simplicitation
join (ALam   s a) (ALam   _ b) = ALam   s $ AJoin a b
join (AApl   s a) (AApl   _ b) = AApl   s $ AJoin a b
join (AQuant a  ) (AQuant b  ) = AQuant   $ AJoin a b
join (AInstn a t) (AInstn b _) = AInstn (AJoin a b) t
-- Collect and sort
join c1 c2 = joinSort $ jCollect (AJoin c1 c2)
  where jCollect (AJoin c3 c4) = jCollect c3 ++ jCollect c4 
        jCollect ann = [ann]
        joinSort = operatorSort AJoin constrJoin


-- | Annotation application
application :: Annotation -> Annotation -> Annotation
application (ALam s f) x | sortIsAnnotation s = eval $ annStrengthen $ foldAnnAlg subsAnnAlg f
                         | sortIsRegion     s = eval $ foldAnnAlg subsRegAlg f
                         | otherwise = rsError "Sort is neither region or annotation!?"
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \d idx -> if d == idx 
                           then annWeaken d x -- Weaken indexes
                           else AVar idx
        }
        -- | Substitute a region variable for a region
        subsRegAlg = idAnnAlg {
          aConstr = \d c -> AConstr $ regVarSubst d x c
        }
application (ATop s) x = (ATop s)
application f    x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: Annotation -> Type -> Annotation
instantiate (AQuant anno) ty = eval $ foldAnnAlg annInstAlg anno
  where annInstAlg = idAnnAlg {
    aLam   = \d s a -> ALam (sortSubstitute d ty s) a,
    aFix   = \d s a -> AFix (sortSubstitute d ty s) a
  } 
instantiate (ATop s) _ = (ATop s)
instantiate a    t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: Int -> Annotation -> Annotation 
project idx (ATuple as) | length as > idx = as !! idx
                        | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as)
project _   (ATop s) = (ATop s)
project idx t    = AProj idx t 


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

----------------------------------------------------------------
-- Subsitution of region variables
----------------------------------------------------------------

-- | Initialize region variables in a constraint set
regVarSubst :: Int -> Annotation -> Constr -> Constr 
regVarSubst d ann c = foldl constrAdd c' insts
  where cIdxs = constrIdxWithVar d c       -- Indexes that contain the to-be instantiated var
        ns    = flip constrIdx c <$> cIdxs -- Get bounds on indexes
        c'    = foldr constrRem c cIdxs    -- Remove cIdxs from c
        aIdxs = eval <$> regVarInst ann <$> (constrIdxToAnn <$> cIdxs)              -- Get new indexes
        insts = constrReIndex (weakenIdx d) 0 <$> uncurry collect <$> zip ns aIdxs  -- Instantiate and weaken
        
        regVarInst :: Annotation -> Annotation -> Annotation
        regVarInst inst (AVar _)    = inst
        regVarInst inst (AProj i a) = AProj i $ regVarInst inst a
        regVarInst inst r = rsError $ "regVarInst: " ++ show inst ++ ", r: " ++ show r