{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics where
import Unbound.Generics.LocallyNameless ( Fresh )
import Rhodium.Blamer.Path
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (Axiom, TyVar, RType, Constraint (Constraint_Inst, Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con, MonoType_Var), PolyType (PolyType_Mono))
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU (ConstraintInfo, HasProperties (addProperty), Property (TypeFamilyReduction))
import Rhodium.Blamer.Heuristics (VotingHeuristic (SingleVoting))
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules (labelResidual, ErrorLabel (ErrorLabel))

import Rhodium.TypeGraphs.Graph (getEdgeFromId)
import Rhodium.Blamer.Path (edgeIdFromPath)
import Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils (buildReductionTrace, getFullTrace, getLastTypeInTrace, getFirstTypeInTrace)
import Data.Maybe (fromJust)
import Debug.Trace (trace)

typeErrorThroughReduction :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo) )
                          => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
typeErrorThroughReduction path = SingleVoting "Type error through type family reduction" f
  where
    f (constraint, eid, ci, gm) = do
      graph <- getGraph
      case constraint of
        Constraint_Inst _ (PolyType_Mono _ pmt) _ -> do
          let ceid = edgeIdFromPath path
          let cedge = getEdgeFromId graph ceid
          let pconstraint = getConstraintFromEdge cedge
          case (pconstraint, labelFromPath path) of
            (Constraint_Unify mf@(MonoType_Fam f fmts _) t _, ErrorLabel "Residual constraint")
              -> return Nothing
            (Constraint_Unify t1 t2 _, ErrorLabel "Incorrect constructors") -> do
              t1Trace <- buildReductionTrace cedge t1
              t2Trace <- buildReductionTrace cedge t2
              case getFullTrace t1Trace t2Trace of
                Nothing -> return Nothing
                Just theTrace -> if typeIsInType (fromJust $ getLastTypeInTrace theTrace) pmt
                  then do
                    let reducedTypeSig = replaceIfEqual (fromJust $ getFirstTypeInTrace theTrace) (fromJust $ getLastTypeInTrace theTrace) pmt
                    return $ Just (5, "Type family reduction type error", constraint, eid, addProperty (TypeFamilyReduction reducedTypeSig theTrace (fromJust $ getFirstTypeInTrace theTrace)) ci, gm)
                  else return Nothing
            _ -> return Nothing
        _                     -> return Nothing

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
