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
import Debug.Trace (trace)
import Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos
import Helium.Syntax.UHA_Range (showRange)
import Data.Maybe (fromMaybe)


buildReductionTrace :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                    => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildReductionTrace e mt = case getMaybeReductionStep mt of
      -- If no own reductions, check args of type family for reductions
      Nothing -> case mt of
          MonoType_Fam{} -> buildNestedSteps e mt
          _                    -> return []
      -- else, we build substituted step components from the step we obtain.
      Just (Step after before mconstr rt) -> do
          (MType after') <- getSubstTypeFull (getGroupFromEdge e) (MType after)
          (MType before') <- getSubstTypeFull (getGroupFromEdge e) (MType before)       
          ih <- buildReductionTrace e before'
          return $ (Step after' before' mconstr rt, 1) : ih

buildNestedSteps :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                   => TGEdge (Constraint ConstraintInfo) -> MonoType -> m ReductionTrace
buildNestedSteps = buildNestedSteps' []
    where
        buildNestedSteps' seen e' mt' =
            case mt' of
                mf@(MonoType_Fam f (m:mts) _) -> do
                    step <- getOneStep e' m
                    case step of
                      Nothing -> do
                          -- diveDeeper dives into the type itself (and recurses)
                          diveDeeper <- buildNestedSteps e' m
                          let resArg = fromMaybe m (getLastTypeInTrace diveDeeper)
                          -- next obtains the next argument of the original type family
                          next <- buildNestedSteps' (resArg:seen) e' (MonoType_Fam f mts Nothing)
                          -- setInsideFam takes the recurses in diveDeeper and deposits them back in the original type family.
                          return $ setInsideFam seen mf diveDeeper ++ next
                      Just (Step after before mconstr rt) -> do
                            ih <- buildNestedSteps' seen e' (MonoType_Fam f (before:mts) Nothing)
                            return ((Step (MonoType_Fam f (seen++(after:mts)) Nothing) (MonoType_Fam f (seen++(before:mts)) Nothing) mconstr rt, 1) : ih)
                _ -> return []
        
        setInsideFam seen mf@(MonoType_Fam f (_:mts) _) ((Step after before constr rt, _):ss) = let
            afterFam = MonoType_Fam f (seen++(after:mts)) Nothing
            beforeFam = MonoType_Fam f (seen++(before:mts)) Nothing
            famStep = Step afterFam beforeFam constr rt
            in (famStep, 1) : setInsideFam seen mf ss
        setInsideFam _ _ [] = []


-- Gets one step.
getOneStep :: (CompareTypes m (RType ConstraintInfo), Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
                  => TGEdge (Constraint ConstraintInfo) -> MonoType -> m (Maybe ReductionStep)
getOneStep e mt = case getMaybeReductionStep mt of
    Nothing -> return Nothing
    Just (Step after before mconstr rt) -> return $ Just $ Step after before mconstr rt

-- Squashes the trace when similar reduction steps are found.
squashTrace :: ReductionTrace -> ReductionTrace 
squashTrace rts = let
    
    groupedRts = groupBy (\(Step _ _ _ rt1, _) (Step _ _ _ rt2, _) -> rt1 == rt2) rts
    in map buildNewStep groupedRts
    where
        buildNewStep [s] = s 
        buildNewStep (s@(Step after _ c rt, _):groupedRt) = let
            (Step _ before _ _, _) = last groupedRt 
            in (Step after before c rt, length (s:groupedRt))

-- Gets last type in the trace
getLastTypeInTrace :: ReductionTrace -> Maybe MonoType
getLastTypeInTrace rt = case rt of
  [] -> Nothing
  xs -> let (Step _ before _ _, _) = last xs in Just before

-- Gets first type in the trace
getFirstTypeInTrace :: ReductionTrace -> Maybe MonoType
getFirstTypeInTrace [] = Nothing
getFirstTypeInTrace ((Step after _ _ _, _):_) = Just after 

-- Name not entirely fitting, gets the "full" trace among two traces.
getFullTrace :: ReductionTrace -> ReductionTrace -> Maybe (Int, ReductionTrace)
getFullTrace [] [] = Nothing
getFullTrace [] xs = Just (1, xs)
getFullTrace xs [] = Just (0, xs)
getFullTrace [(Step (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) _) _ _ _, _)] xs = Just (1, xs)
getFullTrace xs [(Step (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) _) _ _ _, _)] = Just (0, xs)
getFullTrace _ _ = Nothing

-- Maps trace to a message block for type error messages.
traceToMessageBlock :: ReductionTrace -> MessageBlock
traceToMessageBlock rts = MessageCompose $ mapToBlock (1 :: Int) rts
    where
        mapToBlock idx ((Step after before _ rt@(LeftToRight (lhs, rhs) tfi), times):rts')
            = MessageCompose 
                [
                  MessageString (show idx ++ ". " ++ "Applied\t: " ++ show lhs ++ " = " ++ show rhs)
                , MessageString ("\n   From\t: " ++ showMaybeRange tfi)
                , MessageString ("\n   Step\t: " ++ show after ++ " <- " ++ show before)
                , MessageString ("\n   Reason\t: " ++ showReason rt)
                , MessageString ("\n   Amount\t: " ++ timesToString times)
                , MessageString "\n"
                ]
                : mapToBlock (idx + 1) rts'
        mapToBlock idx ((Step after before constr rt@CanonReduction, times):rts')
            = MessageCompose 
                [
                  MessageString (show idx ++ ". " ++ "Step\t: " ++ show after ++ " <- " ++ show before)
                , MessageString ("\n   Constraint\t: " ++ show constr)
                , MessageString ("\n   Reason\t: " ++ showReason rt)
                , MessageString ("\n   Amount\t: " ++ timesToString times)
                ]
                : mapToBlock (idx + 1) rts'
        mapToBlock idx ((Step after before _ rt@(TopLevelImprovement (lhs, rhs) tfi), times):rts')
            = --MessageString (show idx ++ ". " ++ showMaybeRange tfi ++ "\t: " ++ show after ++ " <- " ++ show before ++ "\n   Reason\t: injective top-level improvement" ++ timesToString times ++ "\n.")
              MessageCompose 
                [
                  MessageString (show idx ++ ". " ++ "Applied\t: " ++ show lhs ++ " = " ++ show rhs)
                , MessageString ("\n   From\t: " ++ showMaybeRange tfi)
                , MessageString ("\n   Step\t: " ++ show after ++ " <- " ++ show before)
                , MessageString ("\n   Reason\t: " ++ showReason rt)
                , MessageString ("\n   Amount\t: " ++ timesToString times)
                , MessageString "\n"
                ]
                : mapToBlock (idx + 1) rts'
        mapToBlock _ [] = []

        timesToString t = show t ++ " time" ++ if t == 1 then "" else "s"

        showMaybeRange tfi = case tfi of
            Nothing -> "unkown position"
            Just t -> showRange $ tfiRange t
        
        showReason rt = case rt of
            LeftToRight _ _ -> "left to right application"
            CanonReduction -> "canon reduction"
            TopLevelImprovement _ _ -> "injective top-level improvement"