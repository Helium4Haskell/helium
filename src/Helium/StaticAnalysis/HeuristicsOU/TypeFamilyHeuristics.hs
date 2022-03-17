{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics where
import Unbound.Generics.LocallyNameless ( Fresh )
import Rhodium.Blamer.Path
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (Axiom (Axiom_ClosedGroup), TyVar, RType (MType), Constraint (Constraint_Inst, Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con, MonoType_Var), PolyType (PolyType_Mono))
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Rhodium.Blamer.Heuristics (VotingHeuristic (SingleVoting))
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules (labelResidual, ErrorLabel (ErrorLabel))

import Rhodium.TypeGraphs.Graph (getEdgeFromId)
import Rhodium.Blamer.Path (edgeIdFromPath)
import Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils (buildReductionTrace, getFullTrace, getLastTypeInTrace, getFirstTypeInTrace, squashTrace)
import Data.Maybe (fromJust)
import Debug.Trace (trace)
import Data.List (intercalate)
import Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo
import Helium.StaticAnalysis.Messages.HeliumMessages (freshenRepresentation)
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances (reactClosedTypeFam)
import Helium.Utils.Utils (internalError)

typeErrorThroughReduction :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo) )
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
typeErrorThroughReduction path = SingleVoting "Type error through type family reduction" f
  where
    f (constraint, eid, ci, gm) = do
      graph <- getGraph
      let edge = getEdgeFromId graph eid
      case constraint of
        Constraint_Inst _ (PolyType_Mono _ pmt) _ -> do
          -- Getting edge of erroneous constraint (pconstraint)
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of
            -- PConstraint could not be reduced further
            (cf@(Constraint_Unify mf@(MonoType_Fam _ fmts _) t _), ErrorLabel "Residual constraint") -> do
              let varsInTf = filter isVar fmts
              substVars <- mapM (getSubstTypeFull (getGroupFromEdge cedge) . MType) varsInTf
              -- substVarsMt is all type family applications obtained from vars. They were not reducable.
              let substVarsMt = filter isFam $ map (\(MType m) -> makeCharString m) substVars
              -- Obtain substitution of full type
              [MType freshMf] <- freshenRepresentation . (:[]) <$> getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              --let [MType freshMf] = freshenRepresentation [mf']
              let mf' = makeCharString freshMf
              -- Get potential trace.
              theTrace <- squashTrace <$> buildReductionTrace cedge mf'
              theHint <- buildApartnessHint substVarsMt cf  
              case theTrace of
                [] -> return $ Just (4, "Type family could not be reduced, no trace", constraint, eid, theHint ci, gm)
                trc -> do
                  let Just lastType = getLastTypeInTrace trc
                  let Just firstType = getFirstTypeInTrace trc
                  if typeIsInType lastType pmt
                    then return $ Just (5, "Type family could not be reduced further, trace", constraint, eid, addProperty (TypeFamilyReduction theTrace t lastType firstType) $ theHint ci, gm)
                    else return Nothing
            -- Reduced to simple type but resulted in type error
            (Constraint_Unify t1 t2 _, _) -> do
              (MType t1') <- getSubstTypeFull (getGroupFromEdge edge) (MType t1)
              (MType t2') <- getSubstTypeFull (getGroupFromEdge edge) (MType t2)
              t1Trace <- squashTrace <$> buildReductionTrace edge t1'
              t2Trace <- squashTrace <$> buildReductionTrace edge t2'
              case getFullTrace t1Trace t2Trace of
                Nothing -> return Nothing
                Just (ti, theTrace) -> do
                  let inferredT = makeCharString $ if ti == 0 then t2 else t1
                  let Just lastType = getLastTypeInTrace theTrace
                  let Just firstType = getFirstTypeInTrace theTrace
                  if typeIsInType lastType pmt
                    then return $ Just (7, "Type family reduction type error", constraint, eid, addProperty (TypeFamilyReduction theTrace inferredT lastType firstType) ci, gm)
                    else return Nothing
            _ -> return Nothing
        _                     -> return Nothing
        where
          buildApartnessHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo)) 
                                => [MonoType] -> Constraint ConstraintInfo -> m (ConstraintInfo -> ConstraintInfo)
          buildApartnessHint substVarsMt c@(Constraint_Unify (MonoType_Fam fn fmts _) _ _) = do
            axs <- getAxioms
            
            let (cc@(Constraint_Unify cmf@MonoType_Fam{} _ _), mClosedAxs) = case trace ("SUBSTVARSMT: " ++ show fmts) substVarsMt of
                  [] -> (c, getMaybeClosedAxs axs fn)
                  (mt@(MonoType_Fam mfn _ _) : _) -> (Constraint_Unify mt (MonoType_Con "Char" Nothing) Nothing, getMaybeClosedAxs axs mfn)
                  _ -> internalError "TypeFamilyHeuristics.hs" "typeErrorThroughReduction" "only fams should be here"          

            mApartErr <- case mClosedAxs of
              Nothing -> return Nothing
              Just caxs -> snd <$> reactClosedTypeFam False False cc caxs
            case mApartErr of
              Just mt -> do
                let hint = addHint "probable cause" (show cmf ++ " is not apart from " ++ show mt)
                return hint
              Nothing -> return $ addHint "probable cause" (show cmf ++ " is not reducable")
          buildApartnessHint _ _ = return id

          getMaybeClosedAxs :: [Axiom ConstraintInfo] -> String -> Maybe [Axiom ConstraintInfo]
          getMaybeClosedAxs (Axiom_ClosedGroup fn1 cgaxs: _) fn2
            | fn1 == fn2 = Just cgaxs
          getMaybeClosedAxs (_:axs) fn = getMaybeClosedAxs axs fn
          getMaybeClosedAxs [] _     = Nothing

          isVar MonoType_Var{} = True
          isVar _              = False

          isFam MonoType_Fam{} = True
          isFam _              = False

-- substituteTouchable :: (Fresh m, CompareTypes m (RType ConstraintInfo)) => RType ConstraintInfo -> Groups -> m (RType ConstraintInfo)
-- substituteTouchable mv@(MType (MonoType_Var _ tv _)) grps = do
--   isTch <- isVertexTouchable (tv :: TyVar)
--   case isTch of
--     Nothing -> return mv
--     Just _ -> getSubstTypeFull grps mv



typeIsInType :: MonoType -> MonoType -> Bool
typeIsInType t1 mf@(MonoType_Fam _ mts _) = mf == t1 || any (typeIsInType t1) mts
typeIsInType t1 ma@(MonoType_App m1 m2 _) = ma == t1 || typeIsInType t1 m1 || typeIsInType t1 m2
typeIsInType t1 mc@(MonoType_Con _ _)     = t1 == mc
typeIsInType t1 mv@MonoType_Var{}         = t1 == mv

replaceIfEqual :: MonoType -> MonoType -> MonoType -> MonoType
replaceIfEqual t1 t2 mf@(MonoType_Fam f mts rt) = if t2 == mf then t1 else MonoType_Fam f (map (replaceIfEqual t1 t2) mts) rt
replaceIfEqual t1 t2 ma@(MonoType_App m1 m2 rt) = if t2 == ma then t1 else MonoType_App (replaceIfEqual t1 t2 m1) (replaceIfEqual t1 t2 m2) rt
replaceIfEqual t1 t2 mc@(MonoType_Con _ _)      = if t2 == mc then t1 else mc
replaceIfEqual t1 t2 mv@MonoType_Var{}          = if t2 == mv then t1 else mv

makeCharString :: MonoType -> MonoType
makeCharString (MonoType_App (MonoType_Con "[]" _) (MonoType_Con "Char" _) rt) = MonoType_Fam "String" [] rt
makeCharString (MonoType_App m1 m2 rt) = MonoType_App (makeCharString m1) (makeCharString m2) rt
makeCharString (MonoType_Fam f mts rt) = MonoType_Fam f (map makeCharString mts) rt
makeCharString mt = mt