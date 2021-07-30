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

-- TODO: Rewrite without foldalg for more control over subevals?
-- | Fully evaluate an expression
eval :: DataTypeEnv -> Annotation -> Annotation
eval dEnv ann = foldAnnAlg evalAlg ann
  where evalAlg = idAnnAlg {
    aAdd   = \_ -> add,
    aMinus = \_ -> minus,
    aJoin  = \_ -> join        dEnv,
    aApl   = \_ -> application dEnv,
    aInstn = \_ -> instantiate dEnv,
    aProj  = \_ -> project     dEnv ann,
    aTop   = \_ -> top,
    aBot   = \_ -> bot
  }


-- | Only add when the subannotations are constraints
add :: Annotation -> Annotation -> Annotation
add c1 c2 = let parts1 = addCollect (AAdd c1 c2)
                (constrs, parts2) = partition isConstr parts1
                constr = addConstrs constrs
            in addSort (constr ++ parts2)


-- | Minus of constraint
minus :: Annotation -> RegionVar -> Annotation
minus (AConstr c) r = AConstr $ constrRem (Region r) c
-- Top and bottom
minus (ATop s vs) _ = ATop s vs
minus (ABot s   ) _ = ABot s
-- Cannot eval
minus a r = AMinus a r


-- | Annotation application
application :: DataTypeEnv -> Annotation -> Annotation -> Annotation
application dEnv (ALam lamS f) x = eval dEnv $ foldAnnAlgN (0,-1) subsAnnAlg f
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \(lD,_) idx -> if lD == idx 
                                 then annWeaken lD 0 x -- Weaken indexes
                                 else AVar $ strengthenIdx lD idx,
          aConstr = \(lD,_) c   -> AConstr $ regVarSubst lamS lD x c,
          aTop    = \(lD,_) s c -> ATop s  $ regVarSubst lamS lD x c
        }
-- Make application on join a join of applications
application dEnv (AJoin a b) x = eval dEnv $ AJoin (AApl a x) (AApl b x)
-- Cannot eval
application _ f x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: DataTypeEnv -> Annotation -> Type -> Annotation
instantiate dEnv (AQuant anno) ty = eval dEnv $ foldAnnAlgQuantsN 0 annInstAlg anno
  where annInstAlg = idAnnAlg {
    aBot   = \qD s   -> ABot (sortSubstitute dEnv qD ty s),
    aTop   = \qD s c -> ATop (sortSubstitute dEnv qD ty s) c,
    aLam   = \qD s a -> ALam (sortSubstitute dEnv qD ty s) a,
    aFix   = \qD s a -> AFix (sortSubstitute dEnv qD ty <$> s) a,
    aInstn = \qD a t -> AInstn a (typeSubstitute qD (typeWeaken qD ty) t)
  } 
-- Cannot eval
instantiate _ a t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: DataTypeEnv -> Annotation -> Int -> Annotation -> Annotation 
project _    tmp idx (ATuple as) | length as > idx = as !! idx
                                 | otherwise       = rsError $ "Projection-index out of bounds"
                                                            ++ "\n  Idx: " ++ show idx 
                                                            ++ "\n  Annotation: " ++ (deSymbol $ show $ ATuple as) 
                                                            ++ "\n\n" ++ (deSymbol $ show tmp)                         
-- Moving a join outwards
project dEnv _   idx (AJoin a b) = eval dEnv $ AJoin (AProj idx a) (AProj idx b)
-- Cannot eval
project _    _   idx t = AProj idx t 


-- | Break up top into a value
top :: Sort -> Constr -> Annotation
top SortUnit          _ = AUnit 
top SortConstr        c = AConstr c 
top (SortTuple ss   ) c = ATuple  $ eval emptyDEnv . flip ATop c <$> ss
top (SortQuant s    ) c = AQuant  . eval emptyDEnv $ ATop s c
top (SortLam   s1 s2) c = ALam s1 . eval emptyDEnv $ ATop s2 $ constrAdd (constrWeaken 1 c) (constrInfty $ AnnVar 0)
top s c = ATop s c


-- | Break up bot into a value
bot :: Sort -> Annotation
bot SortUnit          = AUnit 
bot SortConstr        = AConstr constrBot
bot (SortTuple ss   ) = ATuple  $ eval emptyDEnv . ABot <$> ss
bot (SortQuant s    ) = AQuant  . eval emptyDEnv $ ABot s
bot (SortLam   s1 s2) = ALam s1 . eval emptyDEnv $ ABot s2
bot s = ABot s


-- | Join of annotations
join :: DataTypeEnv -> Annotation -> Annotation -> Annotation
-- Cases that consume the other element
join _ _ AUnit    = AUnit
join _ AUnit _    = AUnit 
join _ (ABot _) a = a 
join _ a (ABot _) = a
join _ (ATop   s vs) a = ATop s $ constrJoin (gatherConstraints a) vs
join _ a (ATop   s vs) = ATop s $ constrJoin (gatherConstraints a) vs
-- Complex case
join dEnv a b = 
  let parts1 = ordNub $ joinCollect (AJoin a b)
      (vars, parts2) = partition isVar parts1
      vars' = joinVars vars -- Vars are combined with lams
      (lams,    parts3 ) = partition isLam    parts2
      (qnts,    parts4 ) = partition isQuant  parts3
      (tups,    parts5 ) = partition isTuple  parts4
      (instns,  parts6 ) = partition isInstn  parts5
      (constrs, parts7 ) = partition isConstr parts6
      (regs,    parts8 ) = partition isReg    parts7
      (adds,    parts9)  = partition isAdd    parts8
      (minuss,  parts10) = partition isMinus  parts9
  in joinSort $ eval dEnv <$> concat [ joinLams    lams vars'
                                     , joinInstns  instns -- TODO: Also combine with vars?
                                     , joinQuants  qnts
                                     , joinTuples  tups
                                     , joinConstrs constrs
                                     , joinRegs    regs
                                     , joinAdds    adds
                                     , joinMinuss  minuss
                                     , parts10 ]

----------------------------------------------------------------
-- Subsitution of region variables
----------------------------------------------------------------

-- | Initialize region variables in a constraint set
regVarSubst :: Sort -> Int -> Annotation -> Constr -> Constr 
regVarSubst argS d ann c | sortIsRegion argS = regVarSubst' d ann c
                         | otherwise         = regVarSubst' d (gatherConstraintsTuple ann) c

-- | Initialize region variables in a constraint set
regVarSubst' :: Int -> Annotation -> Constr -> Constr 
regVarSubst' d ann c = constrAdds $ (constrStrengthenN d c'):(constrWeaken d <$> insts)
  where targetIdxs = constrIdxWithVar d c            -- Indexes that contain the to-be instantiated var
        targetBnds = flip constrIdx c <$> targetIdxs -- Bounds on targets
        c'    = foldr constrRem c targetIdxs         -- Remove target indexes  from c

        aIdxs = evalReg. regVarInst ann . constrIdxToAnn <$> targetIdxs -- Indexes with the instantiation
        insts = uncurry collect <$> zip targetBnds aIdxs                 -- Collect indices
        
        regVarInst :: Annotation -> Annotation -> Annotation
        regVarInst inst (AVar _)    = inst
        regVarInst inst (AProj i a) = AProj i $ regVarInst inst a
        regVarInst inst r = rsError $ "regVarInst: " ++ show inst ++ ", r: " ++ show r

        evalReg :: Annotation -> Annotation 
        evalReg (AVar a)              = (AVar a) 
        evalReg (AReg r)              = (AReg r) 
        evalReg (ATuple as)           = (ATuple $ evalReg <$> as) 
        evalReg (AProj i a) = case evalReg a of  
                                  ATuple as | i < length as -> as !! i 
                                            | otherwise     -> rsError $ "Constraint index projection out of bounds: " 
                                                                      ++ "\nIndex: " ++ show i
                                                                      ++ "\nTuple: " ++ show a  
                                  _ -> AProj i a
        evalReg a = rsError $ "Illigal annotation for a constraint index: " ++ show a 
 
----------------------------------------------------------------
-- Join rules
----------------------------------------------------------------

-- | Collect all annotations in a group of joins
joinCollect :: Annotation -> [Annotation]
joinCollect (AJoin a b) = joinCollect a ++ joinCollect b 
joinCollect ann = [ann]

-- | Create a sorted join from a list of annotations
joinSort :: [Annotation] -> Annotation 
joinSort [] = rsError "joinSort called on empty list"
joinSort as = foldl1 AJoin $ sort as

-- | Combine annotation variables
joinVars :: [Annotation] -> [Annotation]
joinVars = ordNub 

-- | Combine annotation variables
joinRegs :: [Annotation] -> [Annotation]
joinRegs = ordNub

-- | Combine annotation additions
joinAdds :: [Annotation] -> [Annotation]
joinAdds []   = []
joinAdds adds = let (as, bs) = unzip $ unAAdd <$> adds
                in [AAdd (joinSort as) (joinSort bs)]

-- | Combine instantiations if the types are equal
joinMinuss :: [Annotation] -> [Annotation]
joinMinuss [] = []
joinMinuss minuss = go $ sortWith (\(AMinus _ r) -> r) minuss
  where go [] = []
        go [AMinus c r] = [AMinus c r] 
        go (AMinus c1 r1:AMinus c2 r2:xs) | r1 == r2  = go $ AMinus (AJoin c1 c2) r1:xs 
                                          | otherwise = (AMinus c1 r1) : go (AMinus c2 r2:xs)
        go _ = error ""

-- | join annotation lambdas
joinLams :: [Annotation] -- ^ Lams
         -> [Annotation] -- ^ Vars
         -> [Annotation]
joinLams [] vars = vars
joinLams lams@(ALam s _:_) vars = [ALam s . joinSort $ (dropLam <$> lams) ++ (varToLam <$> vars)]
  where varToLam (AVar idx) = AApl (AVar $ idx+1) (AVar 0)
        varToLam _ = rsError "Regionsize.joinLams: non-variable in vars"
        dropLam  (ALam _ a) = a
        dropLam _ = rsError "regionSize.joinLams: droplam on non-lam"
joinLams _ _ = rsError "non-lambda in joinLams"

-- | Combine annotation quantifiers
joinQuants :: [Annotation] -> [Annotation]
joinQuants []     = []
joinQuants quants = [AQuant . joinSort $ dropQuant <$> quants]
  where dropQuant (AQuant a) = a
        dropQuant _ = rsError "RegionSize.joinQuants: non-quantifier"

-- | Combine tuples
joinTuples :: [Annotation] -> [Annotation]
joinTuples [] = []
joinTuples tups = let ts = unsafeUnliftTuple <$> tups
                  in [ATuple $ foldl1 (zipWith AJoin) ts] 

-- | Combine instantiations if the types are equal
joinInstns :: [Annotation] -> [Annotation]
joinInstns [] = []
joinInstns instns = go $ sortWith (\(AInstn _ t) -> t) instns
  where go [] = []
        go [AInstn a t] = [AInstn a t] 
        go (AInstn a t1:AInstn b t2:xs) | t1 == t2  = go $ AInstn (AJoin a b) t1:xs 
                                        | otherwise = (AInstn a t1) : go (AInstn b t2:xs)
        go _ = error ""

-- | Combine constrs
joinConstrs :: [Annotation] -> [Annotation]
joinConstrs [] = []
joinConstrs cs = [AConstr . constrJoins $ unAConstr <$> cs]  

----------------------------------------------------------------
-- Addition utilities
----------------------------------------------------------------

-- | Collect all annotations in a group of joins
addCollect :: Annotation -> [Annotation]
addCollect (AAdd a b) = addCollect a ++ addCollect b 
addCollect ann = [ann]

-- | Create a sorted join from a list of annotations
addSort :: [Annotation] -> Annotation 
addSort [] = AConstr constrBot
addSort as = foldl1 AAdd $ sort as

-- | Combine constraint sets
addConstrs :: [Annotation] -> [Annotation]
addConstrs [] = []
addConstrs xs = let result = constrAdds $ unAConstr <$> xs
                in if result == constrBot
                   then []
                   else [AConstr result] 


-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Annotation
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Annotation as A
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Sort as S      
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Evaluate as E
-- import qualified Data.Map.Strict as M
-- E.eval emptyDEnv $ A.ALam SortMonoRegion (A.AApl (A.ALam SortMonoRegion (A.AConstr (M.fromList([(AnnVar 0, Nat 1)])))) (A.AVar 0))
-- E.eval emptyDEnv $ A.ALam SortMonoRegion $ A.ALam S.SortUnit $ (A.AApl (A.ALam SortMonoRegion (A.AConstr (M.fromList([(AnnVar 0, Nat 1)])))) (A.AVar 1))