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
      addEdge edge info
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
               -> do vertices  <- verticesInGroupOf  i
                     constants <- constantsInGroupOf i
                     children  <- childrenInGroupOf  i                     
                     case constants of 
                        [s] -> return (Just (TCon s))               
                        []  -> case children of 
                                  []        -> let rep = fst (head vertices)
                                               in return (Just (TVar rep))
                                  (_, (c1, c2)):_ -> 
                                     do mt1 <- rec (i : history) (TVar c1)
                                        mt2 <- rec (i : history) (TVar c2)
                                        return $ 
                                           do tp1 <- mt1
                                              tp2 <- mt2
                                              return (TApp tp1 tp2)
                        _ -> return Nothing
    TCon s     -> return (Just tp)
    
    TApp t1 t2 -> do mt1 <- rec history t1
                     mt2 <- rec history t2
                     case (mt1,mt2) of 
                       (Just t1',Just t2') -> return (Just $ TApp t1' t2')
                       _                   -> return Nothing
