module Heuristics where

import TypeErrors
import SolveTypeGraph
import EquivalenceGroup
import IsTypeGraph
import Types
import TypeGraphConstraintInfo

getSubstitutedTypes :: IsTypeGraph m info => info -> m (Maybe Tp, Maybe Tp)
getSubstitutedTypes info = 
   do let (t1,t2) = getTwoTypes info
      mt1 <- safeApplySubst t1
      mt2 <- safeApplySubst t2
      return (mt1, mt2)

doWithoutEdge :: IsTypeGraph m info => (EdgeID,info) -> m result -> m result
doWithoutEdge (edge@(EdgeID v1 v2),info) computation =
   do deleteEdge edge       
      result <- computation       
      propagateEquality [v1,v2]
      addEdge edge (Initial info) 
      return result

type HeuristicActions = [HeuristicAction]
data HeuristicAction  = SetHint      TypeErrorInfo
                      | SetTypeError TypeError
                      | RemoveEdge   EdgeID

                   
{- keep a history to avoid non-termination (for type-graphs that contain an infinite type) -}                                           
safeApplySubst :: IsTypeGraph m info => Tp -> m (Maybe Tp)
safeApplySubst = rec [] where 

  rec history tp = case tp of 
    TVar i | i `elem` history 
               -> return Nothing
           | otherwise 
               -> do vertices  <- getVerticesInGroup i
                     constants <- getConstantsInGroup i
                     children  <- getChildrenInGroup i
                     tps       <- case children of
                                     []       -> return [] 
                                     (_,is):_ -> mapM (rec (i : history)) (map TVar is)
                     let tp = case constants of 
                                 []  -> Just . TVar . fst . head $ vertices
                                 [s] -> Just (TCon s)
                                 _   ->  Nothing
                     let tapp t1 t2 = case (t1,t2) of 
                                        (Just t1',Just t2') -> Just (TApp t1' t2')
                                        _                   -> Nothing                                      
                     return (foldl tapp tp tps)
    TCon s     -> return (Just tp)
    TApp t1 t2 -> do mt1 <- rec history t1
                     mt2 <- rec history t2
                     case (mt1,mt2) of 
                       (Just t1',Just t2') -> return (Just $ TApp t1' t2')
                       _                   -> return Nothing
