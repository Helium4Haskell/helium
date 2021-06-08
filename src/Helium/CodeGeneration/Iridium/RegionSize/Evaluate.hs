module Helium.CodeGeneration.Iridium.RegionSize.Evaluate
    ( eval
    ) where 

import Lvm.Core.Type
import Data.List

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
eval dEnv ann = foldAnnAlg evalAlg ann
  where evalAlg = idAnnAlg {
    aAdd   = \_ -> add,
    -- aMinus = \_ -> minus,
    aJoin  = \_ -> join        dEnv,
    aApl   = \_ -> application dEnv,
    aInstn = \_ -> instantiate dEnv,
    aProj  = \_ -> project ann,
    aTop   = \_ -> top,
    aBot   = \_ -> bot
  }


-- | Only add when the subannotations are constraints
add :: Annotation -> Annotation -> Annotation
add c1 c2 = let parts1 = addCollect (AAdd c1 c2)
                (constrs, parts2) = partition isConstr parts1
                constr = addConstrs constrs
            in addSort (constr ++ sort parts2)


-- | Minus of constraint
-- minus :: Annotation -> RegionVar -> Annotation
-- minus (AConstr c) r = AConstr $ constrRem (Region r) c
-- -- Top and bottom
-- minus (ATop s vs) _ = ATop s vs
-- minus (ABot s   ) _ = ABot s
-- -- Cannot eval
-- minus a r = AMinus a r


-- | Annotation application
application :: DataTypeEnv -> Annotation -> Annotation -> Annotation
application dEnv (ALam _ f) x = eval dEnv $ foldAnnAlgN (0,-1) subsAnnAlg f
  where -- | Substitute a variable for an annotation
        subsAnnAlg = idAnnAlg {
          aVar = \(lD,qD) idx -> if lD == idx 
                                 then annWeaken lD qD x -- Weaken indexes
                                 else AVar $ strengthenIdx lD idx,
          aConstr = \(lD,_) c   -> AConstr $ regVarSubst lD x c,
          aTop    = \(lD,_) s c -> ATop s  $ regVarSubst lD x c
        }
-- Top and bottom
application _ (ATop s vs) x | sortIsRegion s = ATop (sortDropLam s) $ constrJoin vs (collect Infty x)
                            | otherwise      = ATop (sortDropLam s) $ constrJoin vs (gatherConstraints x)
-- Cannot eval
application _ f x = AApl f x


-- | Instantiate a type if it starts with a quantification 
instantiate :: DataTypeEnv -> Annotation -> Type -> Annotation
instantiate dEnv (AQuant anno) ty = eval dEnv $ foldAnnAlgQuantsN 0 annInstAlg anno
  where annInstAlg = idAnnAlg {
    aBot   = \qD s   -> ABot (sortSubstitute dEnv qD ty s),
    aTop   = \qD s c -> ATop (sortSubstitute dEnv qD ty s) c,
    aLam   = \qD s a -> ALam (sortSubstitute dEnv qD ty s) a,
    aFix   = \qD s a -> AFix (sortSubstitute dEnv qD ty <$> s) a
  } 
-- Cannot eval
instantiate _ a t = AInstn a t


-- | Only project if subannotation has been evaluated to a tuple
project :: Annotation -> Int -> Annotation -> Annotation 
project tmp idx (ATuple as) | length as > idx = as !! idx
                                 | otherwise       = rsError $ "Projection-index out of bounds\n Idx: " ++ show idx ++ "\n Annotation: " ++ (show $ ATuple as) ++ "\n\n" ++ (show tmp)                         
-- Moving a join outwards
project _   idx (AJoin a b) = joinSort $ AProj idx <$> joinCollect (AJoin a b) 
-- Cannot eval
project _   idx t = AProj idx t 


-- | Break up top into a value
top :: Sort -> Constr -> Annotation
top SortUnit          _ = AUnit 
top SortConstr        c = AConstr c 
top (SortTuple ss   ) c = ATuple  $ flip ATop c <$> ss
top (SortQuant s    ) c = AQuant  $ ATop s c
-- TODO: This maybe prevent caputure a variable to top
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


-- | Join of annotations
join :: DataTypeEnv -> Annotation -> Annotation -> Annotation
-- Cases that consume the other element
join _    _ AUnit     = AUnit
join _    AUnit _     = AUnit 
join _    (ABot _)  a = a 
join _    a  (ABot _) = a
join _    (ATop   s v1) (ATop   _ v2) = ATop s  $ constrJoin v1 v2
join _    (ATop   s vs) a             = ATop s  $ constrJoin (gatherConstraints a) vs
join _    a             (ATop   s vs) = ATop s  $ constrJoin (gatherConstraints a) vs
-- Complex case
join _    a             b             = 
  let parts1 = joinCollect (AJoin a b)
      (vars, parts2) = partition isVar parts1
      vars' = joinVars vars -- Vars are combined with lams
      (lams, parts3) = partition isLam parts2
      lam = joinLams lams vars'
      (qnts, parts4) = partition isQuant parts3
      qnt = joinQuants qnts
      (apls, parts5) = partition isApl parts4
      apl = joinApls apls
      (tups, parts6) = partition isTuple parts5
      tup = joinTuples tups
      (instns, parts7) = partition isInstn parts6
      instns' = joinInstns instns
      (constrs, parts8) = partition isConstr parts7
      constr = joinConstrs constrs
  in joinSort (lam ++ qnt ++ apl ++ tup ++ instns' ++ constr ++ parts8)

----------------------------------------------------------------
-- Subsitution of region variables
----------------------------------------------------------------

-- | Initialize region variables in a constraint set
regVarSubst :: Int -> Annotation -> Constr -> Constr 
regVarSubst d ann c = foldl constrAdd (constrStrengthenN d c') (constrWeaken d <$> insts)
  where cIdxs = constrIdxWithVar d c       -- Indexes that contain the to-be instantiated var
        ns    = flip constrIdx c <$> cIdxs -- Get bounds on indexes
        c'    = foldr constrRem c cIdxs             -- Remove target indexes (cIdxs) from c
        aIdxs = evalReg <$> regVarInst ann <$> (constrIdxToAnn <$> cIdxs) -- Make new indexes
        insts = uncurry collect <$> zip ns aIdxs    -- Instantiate variables
        
        regVarInst :: Annotation -> Annotation -> Annotation
        regVarInst inst (AVar _)    = inst
        regVarInst inst (AProj i a) = AProj i $ regVarInst inst a
        regVarInst inst r = rsError $ "regVarInst: " ++ show inst ++ ", r: " ++ show r

        evalReg :: Annotation -> Annotation
        evalReg (AVar a)              = (AVar a)
        evalReg (AReg r)              = (AReg r)
        evalReg (ATuple as)           = (ATuple $ evalReg <$> as)
        evalReg (AProj _ AUnit)       = AUnit
        evalReg (AProj i a) = case evalReg a of 
                                  ATuple as | i < length as -> as !! i
                                            | otherwise     -> rsError $ "Constraint index projection out of bounds"
                                  _ -> AProj i a
        evalReg a = rsError $ "Illigal annotation for a constraint index: " ++ show a

----------------------------------------------------------------
-- Join utilities
----------------------------------------------------------------

-- | Collect all annotations in a group of joins
joinCollect :: Annotation -> [Annotation]
joinCollect (AJoin a b) = joinCollect a ++ joinCollect b 
joinCollect ann = [ann]

-- | Create a sorted join from a list of annotations
joinSort :: [Annotation] -> Annotation 
joinSort [] = rsError "??"
joinSort as = foldl1 AJoin $ sort as

-- | Combine annotation variables
joinVars :: [Annotation] -> [Annotation]
joinVars = nub

-- | join annotation lambdas
joinLams :: [Annotation] -- ^ Lams
         -> [Annotation] -- ^ Vars
         -> [Annotation]
joinLams [] vars = vars
joinLams lams@(ALam s _:_) vars = [ALam s . joinSort $ lams ++ (varToLam <$> vars)]
  where varToLam (AVar idx) = AApl (AVar $ idx+1) (AVar 0)
        varToLam _ = rsError "Regionsize.joinLams: non-variable in vars"
joinLams _ _ = rsError "non-lambda in joinLams"

-- | Combine annotation quantifiers
joinQuants :: [Annotation] -> [Annotation]
joinQuants []     = []
joinQuants quants = [AQuant . joinSort $ dropQuant <$> quants]
  where dropQuant (AQuant a) = a
        dropQuant _ = rsError "RegionSize.joinQuants: non-quantifier"

-- | Combine annotation applications
joinApls :: [Annotation] -> [Annotation]
joinApls []   = []
joinApls apls = let (fs, xs) = unzip $ unApl <$> apls
                in [AApl (joinSort fs) (joinSort xs)]
  where unApl (AApl f x) = (f,x)
        unApl _ = rsError "RegionSize.joinApls: non-application"

-- | Combine tuples
joinTuples :: [Annotation] -> [Annotation]
joinTuples [] = []
joinTuples tups = let ts = unsafeUnliftTuple <$> tups
                  in foldl1 (zipWith AJoin) ts 

-- | Combine instantiations
joinInstns :: [Annotation] -> [Annotation]
joinInstns [] = []
joinInstns instns = instns

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
addSort [] = rsError "??"
addSort as = foldl1 AAdd $ sort as

-- | Combine constraint sets
addConstrs :: [Annotation] -> [Annotation]
addConstrs [] = []
addConstrs xs = [AConstr . constrAdds $ unAConstr <$> xs] 

----------------------------------------------------------------
-- Other utilities
----------------------------------------------------------------

-- | Gather constraints on local regions from an annotation 
gatherConstraints :: Annotation -> Constr
gatherConstraints a = let locals = constrInfty <$> gatherLocals a
                          annvrs = constrInfty <$> gatherBinds a
                      in constrJoins $ locals ++ annvrs
  

-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Annotation
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Annotation as A
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Sort as S      
-- import qualified Helium.CodeGeneration.Iridium.RegionSize.Evaluate as E
-- import qualified Data.Map as M
-- E.eval emptyDEnv $ A.ALam SortMonoRegion (A.AApl (A.ALam SortMonoRegion (A.AConstr (M.fromList([(AnnVar 0, Nat 1)])))) (A.AVar 0))
-- E.eval emptyDEnv $ A.ALam SortMonoRegion $ A.ALam S.SortUnit $ (A.AApl (A.ALam SortMonoRegion (A.AConstr (M.fromList([(AnnVar 0, Nat 1)])))) (A.AVar 1))