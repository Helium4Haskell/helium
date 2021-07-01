module Helium.CodeGeneration.Iridium.RegionSize.Fixpoint
where

import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate

import Data.List (sort, elemIndex)
import Data.Maybe (fromJust, catMaybes)
import qualified Data.Map.Strict as M

import System.IO.Unsafe

max_iterations :: Int
max_iterations = 10

----------------------------------------------------------------
-- Solving fixpoints
----------------------------------------------------------------

-- | Fill top with local variables in scope
solveFixpoints ::  DataTypeEnv -> Annotation -> Annotation
solveFixpoints dEnv = eval dEnv . go constrBot
    where go scope (ALam   s a) = ALam s $ go (constrAdd (constrInfty $ AnnVar 0) (weakenScope scope)) a  
          go scope (ATuple  as) = ATuple $ go scope <$> as
          go scope (AProj  i a) = AProj i $ go scope a 
          go scope (AApl   a b) = AApl   (go scope a) (go scope b) 
          go scope (AAdd   a b) = AAdd   (go scope a) (go scope b)  
          go scope (AJoin  a b) = AJoin  (go scope a) (go scope b)
          go scope (AQuant a  ) = AQuant (go scope a)
          go scope (AInstn a t) = AInstn (go scope a) t
          go scope (AFix   s v) = ATuple . solveFixpoint dEnv scope s $ go scope <$> v
          go scope (AMinus a r) = AMinus (go scope a) r
          go _     ann = ann

-- | Weaken all region variables in the constraint set
weakenScope :: Constr -> Constr
weakenScope = M.mapKeys weakenKey
   where
     weakenKey (AnnVar n) = AnnVar $ n + 1
     weakenKey others     = others

-- | Solve a group of fixpoints
solveFixpoint :: DataTypeEnv -> Constr -> [Sort] -> [Annotation] -> [Annotation]
solveFixpoint dEnv scope sorts fixes = 
        let bot = ABot s
        in fixIterate 0 bot $ ATuple fixes
    where s = SortTuple sorts
          c = foldr constrAdd scope $ constrInfty <$> gatherLocals (ATuple fixes)  

          fixIterate :: Int -> Annotation -> Annotation -> [Annotation]
          fixIterate n  state fs | n >= max_iterations = unsafePerformIO $ do 
                                                            appendFile "C:\\Users\\hanno\\Desktop\\fixpoints.csv" "0\n"
                                                            return $ mapWithIndex (\ i _ -> AProj i $ ATop s c) fixes 
                                 | otherwise =
              let res = eval dEnv $ AApl (ALam s fs) state
              in if res == state
                 then unsafePerformIO $ do 
                        appendFile "C:\\Users\\hanno\\Desktop\\fixpoints.csv" "1\n"
                        return $ unsafeUnliftTuple res
                 else fixIterate (n+1) res fs 

----------------------------------------------------------------
-- Fixpoint simplification
----------------------------------------------------------------

-- | Solve all the fixpoints in an annotation
inlineFixpoints :: Annotation -> Annotation
inlineFixpoints = foldAnnAlgQuants fixAlg
    where fixAlg = idAnnAlg {
        aProj = \_ i a  -> case a of
                             AFix ss as -> AProj i $ removeUnused i ss as
                             _ -> AProj i a,
        aFix  = \_ s as -> AFix s . inlineFixpoint.inlineFixpoint$inlineFixpoint as
    }

inlineFixpoint :: [Annotation] -> [Annotation]
inlineFixpoint anns = let isRec = checkRecursive <$> anns
                      in fillInNonRec isRec anns <$> anns

fillInNonRec :: [Bool] -> [Annotation] -> Annotation -> Annotation 
fillInNonRec isRec fixes = foldAnnAlgN (0,-1) fillAlg
    where fillAlg = idAnnAlg {
        aProj = \(lD,_) i a -> 
            case a of
                AVar idx -> if idx == lD && not (isRec !! i)
                            then annWeaken lD 0 $ fixes !! i
                            else AProj i a
                _ -> AProj i a
    }

-- | Check if a part of a fixpoint is recursive
checkRecursive :: Annotation -> Bool
checkRecursive ann = (length $ findFixBinds ann) > 0  

-- | Which indices of the fixpoint are used
findFixBinds :: Annotation -> [Int]
findFixBinds = foldAnnAlgLamsN 0 countAlg
    where countAlg = AnnAlg {
        aVar    = \d idx   -> if d == idx
                              then [-1]
                              else [],
        aReg    = \_ _   -> [],
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> a ++ b,
        aConstr = \d c   -> constrFixBinds d c,
        aUnit   = \_     -> [],
        aTuple  = \_ as  -> concat as,
        aProj   = \_ i a -> case a of
                              [-1] -> [i]
                              _ -> a,
        aAdd    = \_ a b -> a ++ b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> a ++ b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \d _ c -> constrFixBinds d c,
        aBot    = \_ _   -> [],
        aFix    = \_ _ a -> concat a   
    }

-- | Find fix binds in constraint set 
constrFixBinds :: Int -> Constr -> [Int]
constrFixBinds d c = catMaybes $ go <$> M.keys c
   where go (AnnVar _  ) = Nothing
         go (Region _  ) = Nothing
         go (CnProj i k) = 
             case k of
                 AnnVar idx | idx == d -> Just i
                 _ -> go k


-- | Remove unused indexes in a fixpoint
removeUnused :: Int -> [Sort] -> [Annotation] -> Annotation
removeUnused targetIdx ss as = AFix usedSrts $ renameUsed usedIdxs <$> usedAnns
    where usedIdxs = sort $ go (findFixBinds <$> as) [] [targetIdx]
          usedAnns = foldr (\i as' -> (as !! i) : as') [] usedIdxs
          usedSrts = foldr (\i ss' -> (ss !! i) : ss') [] usedIdxs
          go _    seen []       = seen
          go rels seen (x:todo) = if x `elem` seen
                                  then go rels seen todo
                                  else go rels (x:seen) (todo ++ (rels !! x))

-- | Change the index of the fixpoint
renameUsed :: [Int] -> Annotation -> Annotation
renameUsed usedIdxs = foldAnnAlgLamsN 0 renameAlg
    where renameAlg = idAnnAlg {
        aProj   = \d i a -> case a of
                              AVar idx | idx == d  -> AProj (fromJust $ elemIndex i usedIdxs) (AVar idx)
                                       | otherwise -> AProj i (AVar idx) 
                              _ -> AProj i a
    }
