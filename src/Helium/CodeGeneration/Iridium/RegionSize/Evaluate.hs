module Helium.CodeGeneration.Iridium.RegionSize.Evaluate
    ( eval
    ) where 

import Lvm.Core.Type
import Data.List

import Helium.CodeGeneration.Iridium.Region.RegionVar

import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils

----------------------------------------------------------------
-- Evalutation
----------------------------------------------------------------

-- | Fully evaluate an expression
eval :: DataTypeEnv -> Annotation -> Annotation
eval dEnv = foldAnnAlg evalAlg
  where evalAlg = idAnnAlg {
    aAdd   = \_ -> add,
    aMinus = \_ -> minus,
    aJoin  = \_ -> join        dEnv,
    aApl   = \_ -> application dEnv,
    aInstn = \_ -> instantiate dEnv,
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
join :: DataTypeEnv -> Annotation -> Annotation -> Annotation
-- Join with constants
join _    _ AUnit     = AUnit
join _    AUnit _     = AUnit 
join _    (ABot _)  a = a 
join _    a  (ABot _) = a 
join _    (ATop   _ vs) (AConstr  c2) = AConstr $ constrJoin vs c2
join _    (AConstr  c1) (ATop   _ vs) = AConstr $ constrJoin c1 vs
join _    (ATop   s v1) (ATop   _ v2) = ATop s  $ constrJoin v1 v2
join _    (ATop   s vs) _             = ATop s vs
join _    _             (ATop   s vs) = ATop s vs
-- Constraint set join
join _    (AConstr  c1) (AConstr  c2) = AConstr $ constrJoin c1 c2
-- Join-simplicitation
join _    (AVar   i1  ) (AVar   i2  ) | i1 == i2  = AVar i1
                                 | otherwise = AJoin (AVar i1) (AVar i2) 
join _    (ALam   s1 a) (ALam   s2 b) | s1 == s2  = ALam s1 $ AJoin a b
                                 | otherwise = operatorSort AJoin constrJoin [ALam s1 a, ALam s2 b]
join _    (AApl   s  a) (AApl   _  b) = AApl   s $ AJoin a b
join _    (AQuant a   ) (AQuant b   ) = AQuant   $ AJoin a b
join _    (AInstn a  t) (AInstn b  _) = AInstn (AJoin a b) t
join dEnv (ATuple as  ) (ATuple bs  ) = eval dEnv . ATuple $ zipWith AJoin as bs
join _    (AProj  i1 a) (AProj  i2 b) | i1 == i2  = AProj i1 (AJoin a b)
                                 | otherwise = operatorSort AJoin constrJoin [AProj i1 a, AProj i2 b]
-- Collect and sort       
join _ c1 c2 = joinSort $ jCollect (AJoin c1 c2)
  where jCollect (AJoin c3 c4) = jCollect c3 ++ jCollect c4 
        jCollect ann = [ann]
        joinSort = operatorSort AJoin constrJoin


-- | Annotation application
-- TODO: Bug: If lamS == () then region is not removed from constrs or top
application :: DataTypeEnv -> Annotation -> Annotation -> Annotation
application dEnv (ALam lamS f) x | sortIsAnnotation lamS = eval dEnv $ foldAnnAlgN (0,-1) subsAnnAlg f
                                 | sortIsRegion     lamS = eval dEnv $ foldAnnAlgN (0,-1) subsRegAlg f
                                 | otherwise = rsError "Sort is neither region or annotation!?"
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \(lD,qD) idx -> if lD == idx 
                                 then annWeaken lD qD x -- Weaken indexes
                                 else AVar $ strengthenIdx lD idx,
          aConstr = \(lD,_) c   -> AConstr $ constrStrengthenN lD c
        }
        -- | Substitute a region variable for a region
        subsRegAlg = idAnnAlg {
          aVar    = \(lD,_) idx -> AVar $ strengthenIdx lD idx,
          aConstr = \(lD,_) c   -> AConstr $ regVarSubst lD x c,
          aTop    = \(lD,_) s c -> ATop s  $ regVarSubst lD x c
        }
-- Top and bottom
application _ (ATop s vs) x | sortIsRegion s = ATop (sortDropLam s) $ constrAdd (collect Infty x) vs
                            | otherwise      = ATop (sortDropLam s) vs
-- Cannot eval
application _ f x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: DataTypeEnv -> Annotation -> Type -> Annotation
instantiate dEnv (AQuant anno) ty = eval dEnv $ foldAnnAlgQuantsN 0 annInstAlg anno
  where annInstAlg = idAnnAlg {
    aBot   = \qD s   -> ABot (sortSubstitute dEnv qD ty s),
    aTop   = \qD s c -> ATop (sortSubstitute dEnv qD ty s) c,
    aLam   = \qD s a -> ALam (sortSubstitute dEnv qD ty s) a,
    aFix   = \qD s a -> AFix (sortSubstitute dEnv qD ty s) a
  } 
-- Cannot eval
instantiate _ a t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: Int -> Annotation -> Annotation 
-- project _   AUnit       = AUnit -- TODO: Check if this is sound, if missing causes an issue in region eval
project idx (ATuple as) | length as > idx = as !! idx
                        | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as)
-- Cannot eval
project idx t = AProj idx t 


-- | Break up top into a value
top :: Sort -> Constr -> Annotation
top SortUnit          _ = AUnit 
top SortConstr        c = AConstr c 
top (SortTuple ss   ) c = ATuple  $ flip ATop c <$> ss
top (SortQuant s    ) c = AQuant  $ ATop s c
-- top (SortLam   s1 s2) c = ALam s1 $ ATop s2 c
top s c = ATop s c

-- | Break up bot into a value
bot :: Sort -> Annotation
bot SortUnit          = AUnit 
bot SortConstr        = AConstr constrBot
bot (SortTuple ss   ) = ATuple  $ ABot <$> ss
bot (SortQuant s    ) = AQuant  $ ABot s
bot (SortLam   s1 s2) = ALam s1 $ ABot s2
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
regVarSubst d ann c = foldl constrAdd (constrStrengthenN d c') (constrWeaken d <$> insts)
  where cIdxs = constrIdxWithVar d c       -- Indexes that contain the to-be instantiated var
        ns    = flip constrIdx c <$> cIdxs -- Get bounds on indexes
        c'    = foldr constrRem c cIdxs             -- Remove target indexes (cIdxs) from c
        aIdxs = eval emptyDEnv <$> regVarInst ann <$> (constrIdxToAnn <$> cIdxs) -- Make new indexes
        insts = uncurry collect <$> zip ns aIdxs    -- Instantiate variables
        
        regVarInst :: Annotation -> Annotation -> Annotation
        regVarInst inst (AVar _)    = inst
        regVarInst inst (AProj i a) = AProj i $ regVarInst inst a
        regVarInst inst r = rsError $ "regVarInst: " ++ show inst ++ ", r: " ++ show r