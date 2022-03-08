{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils where

import Rhodium.TypeGraphs.GraphProperties (CompareTypes, HasTypeGraph)
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (RType (MType), Axiom, TyVar, Constraint (Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con), ReductionTrace, ReductionStep (Step), ReductionType (LeftToRight, CanonReduction, TopLevelImprovement), getMaybeReductionStep)
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU (ConstraintInfo)
import Unbound.Generics.LocallyNameless (Fresh)
import Rhodium.TypeGraphs.Graph (TGEdge, getGroupFromEdge)
import Helium.StaticAnalysis.Messages.Messages (MessageBlock (MessageString, MessageCompose))
import Rhodium.TypeGraphs.GraphUtils (getSubstTypeFull)
import Data.List (groupBy)


buildReductionTrace :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                    => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildReductionTrace e mt = case getMaybeReductionStep mt of
      Nothing -> case mt of
          MonoType_Fam{} -> buildNestedSteps e mt
          _                    -> return []
      Just (Step after before mconstr rt) -> do
          (MType trAfter) <- getSubstTypeFull (getGroupFromEdge e) (MType after)
          (MType trBefore) <- getSubstTypeFull (getGroupFromEdge e) (MType before)          
          trConstr <- case mconstr of 
                Just (Constraint_Unify sm1 sm2 _) -> do
                    (MType trConstrLeft) <- getSubstTypeFull (getGroupFromEdge e) (MType sm1)
                    (MType trConstrRight) <- getSubstTypeFull (getGroupFromEdge e) (MType sm2)
                    return $ Just $ Constraint_Unify trConstrLeft trConstrRight Nothing
          ih <- buildReductionTrace e trBefore
          return $ (Step trAfter trBefore trConstr rt, 1) : ih

buildNestedSteps :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                   => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildNestedSteps = buildNestedSteps' []
    where
        buildNestedSteps' seen e' mt' = do
            (MType mt'') <- getSubstTypeFull (getGroupFromEdge e') (MType mt')
            case mt'' of
                (MonoType_Fam f (m:mts) _) -> do
                    step <- getOneStep e' m
                    case step of
                      Nothing -> buildNestedSteps' (m:seen) e' (MonoType_Fam f mts Nothing)
                      Just (Step after before mconstr rt) -> do
                            ih <- buildNestedSteps' (before:seen) e' (MonoType_Fam f mts Nothing)
                            return ((Step (MonoType_Fam f (seen++(after:mts)) Nothing) (MonoType_Fam f (seen++(before:mts)) Nothing) mconstr rt, 1) : ih)
                _ -> return []


getOneStep :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                  => TGEdge (Constraint ConstraintInfo) -> MonoType -> m (Maybe ReductionStep)
getOneStep e mt = case getMaybeReductionStep mt of
    Nothing -> return Nothing
    Just (Step after before mconstr rt) -> do
        (MType trAfter) <- getSubstTypeFull (getGroupFromEdge e) (MType after)
        (MType trBefore) <- getSubstTypeFull (getGroupFromEdge e) (MType before)
        trConstr <- case mconstr of 
                Just (Constraint_Unify sm1 sm2 _) -> do
                    (MType trConstrLeft) <- getSubstTypeFull (getGroupFromEdge e) (MType sm1)
                    (MType trConstrRight) <- getSubstTypeFull (getGroupFromEdge e) (MType sm2)
                    return $ Just $ Constraint_Unify trConstrLeft trConstrRight Nothing
        return $ Just $ Step trAfter trBefore trConstr rt

squashTrace :: ReductionTrace -> ReductionTrace 
squashTrace rts = let
    
    groupedRts = groupBy (\(Step _ _ _ rt1, _) (Step _ _ _ rt2, _) -> rt1 == rt2) rts
    in map buildNewStep groupedRts
    where
        buildNewStep [s] = s 
        buildNewStep (s@(Step after _ c rt, _):groupedRt) = let
            (Step _ before _ _, _) = last groupedRt 
            in (Step after before c rt, length (s:groupedRt))

getLastTypeInTrace :: ReductionTrace -> Maybe MonoType
getLastTypeInTrace rt = case rt of
  [] -> Nothing
  xs -> let (Step _ before _ _, _) = last xs in Just before

getFirstTypeInTrace :: ReductionTrace -> Maybe MonoType
getFirstTypeInTrace [] = Nothing
getFirstTypeInTrace ((Step after _ _ _, _):_) = Just after 

getFullTrace :: ReductionTrace -> ReductionTrace -> Maybe ReductionTrace
getFullTrace [] [] = Nothing
getFullTrace [] xs = Just xs
getFullTrace xs [] = Just xs
getFullTrace [(Step (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) _) _ _ _, _)] xs = Just xs
getFullTrace xs [(Step (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) _) _ _ _, _)] = Just xs
getFullTrace _ _ = Nothing

traceToMessageBlock :: ReductionTrace -> MessageBlock
traceToMessageBlock rts = let
    in MessageCompose $ mapToBlock (1 :: Int) "" rts
    where
        mapToBlock idx pre ((Step after before _ (LeftToRight _), times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ show after ++ " <--- " ++ show before ++ ". Reason: left to right application. " ++ timesToString times ++ "\n")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock idx pre ((Step after before constr CanonReduction, times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ show after ++ " <--- " ++ show before ++ " in constraint: " ++ show constr ++ ". Reason: canon reduction" ++ timesToString times ++"\n.")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock idx pre ((Step after before _ TopLevelImprovement, times):rts')
            = MessageString (pre ++ show idx ++ ". " ++ show after ++ " <--- " ++ show before ++ ". Reason: injective top-level improvement" ++ timesToString times ++ "\n.")
                : mapToBlock (idx + 1) pre rts'
        mapToBlock _ _ [] = []

        timesToString t = if t == 1 then "" else "Applied " ++ show t ++ " times."