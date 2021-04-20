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
    aProj  = \_ -> project,
    aTop   = \_ -> top,
    aBot   = \_ -> bot
  }


-- | Only add when the subannotations are constraints
add :: Annotation -> Annotation -> Annotation
add (AConstr  c1) (AConstr  c2) = AConstr $ constrAdd c1 c2
-- Top and bottom
add (ATop   _ vs) (AConstr  c2) = AConstr $ constrAdd vs c2
add (AConstr  c1) (ATop   _ vs) = AConstr $ constrAdd c1 vs
add (ATop s   v1) (ATop   _ v2) = ATop s  $ constrAdd v1 v2
add (ATop s   vs) _             = ATop s vs
add _             (ATop   s vs) = ATop s vs
add (ABot _) a = a
add a (ABot _) = a
-- Two non-constraint sets, sort
add c1  c2 = addSort $ aCollect (AAdd c1 c2)
  where aCollect (AAdd c3 c4) = aCollect c3 ++ aCollect c4 
        aCollect ann = [ann]
        addSort = operatorSort AAdd constrAdd


-- | Minus of constraint
minus :: Annotation -> RegionVar -> Annotation
minus (AConstr c) r = AConstr $ constrRem (Region r) c
-- Top and bottom
minus (ATop s vs) _ = ATop s vs
minus (ABot s   ) _ = ABot s
-- Cannot eval
minus a r = AMinus a r


-- | Join of annotations
join :: Annotation -> Annotation -> Annotation
-- Join with constants
join _ AUnit     = AUnit
join AUnit _     = AUnit 
join (ABot _)  a = a 
join a  (ABot _) = a 
join (ATop   _ vs) (AConstr  c2) = AConstr $ constrJoin vs c2
join (AConstr  c1) (ATop   _ vs) = AConstr $ constrJoin c1 vs
join (ATop   s v1) (ATop   _ v2) = ATop s  $ constrJoin v1 v2
join (ATop   s vs) _             = ATop s vs
join _             (ATop   s vs) = ATop s vs
-- Constraint set join
join (AConstr  c1) (AConstr  c2) = AConstr $ constrJoin c1 c2
-- Join-simplicitation
join (ALam   s1 a) (ALam   s2 b) | s1 == s2 = ALam s1 $ AJoin a b
                                 | otherwise = operatorSort AJoin constrJoin [ALam s1 a, ALam s2 b]
join (AApl   s  a) (AApl   _  b) = AApl   s $ AJoin a b
join (AQuant a   ) (AQuant b   ) = AQuant   $ AJoin a b
join (AInstn a  t) (AInstn b  _) = AInstn (AJoin a b) t
join (ATuple as  ) (ATuple bs  ) = eval . ATuple $ zipWith AJoin as bs
join (AProj  i1 a) (AProj  i2 b) | i1 == i2  = AProj i1 (AJoin a b)
                                 | otherwise = operatorSort AJoin constrJoin [AProj i1 a, AProj i2 b]
-- Collect and sort       
join c1 c2 = joinSort $ jCollect (AJoin c1 c2)
  where jCollect (AJoin c3 c4) = jCollect c3 ++ jCollect c4 
        jCollect ann = [ann]
        joinSort = operatorSort AJoin constrJoin


-- | Annotation application
application :: Annotation -> Annotation -> Annotation
application (ALam lamS f) x | sortIsAnnotation lamS = eval $ annStrengthen $ foldAnnAlgN 0 subsAnnAlg f
                            | sortIsRegion     lamS = eval $ annStrengthen $ foldAnnAlgN 0 subsRegAlg f
                            | otherwise = rsError "Sort is neither region or annotation!?"
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \d idx -> if d == idx 
                           then annWeaken (d+1) x -- Weaken indexes
                           else AVar idx
        }
        -- | Substitute a region variable for a region
        subsRegAlg = idAnnAlg {
          aConstr = \d c   -> AConstr $ regVarSubst d x c,
          aTop    = \d s c -> ATop s  $ regVarSubst d x c
        }

-- Top and bottom
application (ATop s vs) x | sortIsRegion s = ATop (sortDropLam s) $ constrAdd (collect Infty x) vs
                          | otherwise      = ATop (sortDropLam s) vs
application (ABot s) _ = (ABot $ sortDropLam s)
-- Cannot eval
application f x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: Annotation -> Type -> Annotation
instantiate (AQuant anno) ty = eval $ foldAnnAlg annInstAlg anno
  where annInstAlg = idAnnAlg {
    aLam   = \d s a -> ALam (sortSubstitute d ty s) a,
    aFix   = \d s a -> AFix (sortSubstitute d ty s) a
  } 
-- Cannot eval
instantiate a t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: Int -> Annotation -> Annotation 
project _   AUnit       = AUnit -- TODO: Check if this is sound, if missing causes an issue in region eval
project idx (ATuple as) | length as > idx = as !! idx
                        | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as)
-- Cannot eval
project idx t = AProj idx t 


-- | Break up top into a value
top :: Sort -> Constr -> Annotation
top SortUnit       c = AUnit 
top SortConstr     c = AConstr c 
top (SortTuple ss) c = ATuple $ flip ATop c <$> ss
top (SortQuant s ) c = AQuant $ ATop s c
top s c = ATop s c

-- | Break up bot into a value
bot :: Sort -> Annotation
bot SortUnit       = AUnit 
bot SortConstr     = AConstr constrBot
bot (SortTuple ss) = ATuple $ ABot <$> ss
bot (SortQuant s ) = AQuant $ ABot s
bot s = ABot s

----------------------------------------------------------------
-- Evalutation utilities
----------------------------------------------------------------

-- | Ordering of binary operator operands, compute all computable operators
operatorSort :: (Annotation -> Annotation -> Annotation)
             -> (Constr -> Constr -> Constr)
             -> [Annotation] 
             -> Annotation
operatorSort op evalF xs = -- Compose list (tops, bots then others)
                           let list = if length tops > 0 && length bots > 0
                                      then compTop : (bots !! 0) : sort others3
                                      else if length tops > 0
                                           then compTop : sort others3
                                           else sort others3
                           -- Combine list into single annotation
                           in if length list == 0 
                              then compConstr
                              else if compConstr /= AConstr constrBot 
                                  then foldl op compConstr  $ list
                                  else foldl op (head list) $ tail list
  where (constrs, others1) = partition isConstr xs
        (tops   , others2) = partition isTop others1  
        (bots   , others3) = partition isBot others2  
        compConstr = AConstr      $ foldr (\(AConstr a)  -> evalF a                 ) (constrBot         ) constrs
        compTop    = uncurry ATop $ foldr (\(ATop s a) b -> (s, constrAdd a $ snd b)) (SortUnit,constrBot) tops

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
        insts = constrWeaken (d+1) <$> uncurry collect <$> zip ns aIdxs  -- Instantiate and weaken
        
        regVarInst :: Annotation -> Annotation -> Annotation
        regVarInst inst (AVar _)    = inst
        regVarInst inst (AProj i a) = AProj i $ regVarInst inst a
        regVarInst inst r = rsError $ "regVarInst: " ++ show inst ++ ", r: " ++ show r