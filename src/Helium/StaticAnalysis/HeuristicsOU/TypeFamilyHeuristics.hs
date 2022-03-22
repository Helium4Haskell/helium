{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
module Helium.StaticAnalysis.HeuristicsOU.TypeFamilyHeuristics where
import Unbound.Generics.LocallyNameless ( Fresh )
import Rhodium.Blamer.Path
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (Axiom (Axiom_ClosedGroup), TyVar, RType (MType), Constraint (Constraint_Inst, Constraint_Unify), MonoType (MonoType_Fam, MonoType_App, MonoType_Con, MonoType_Var), PolyType (PolyType_Mono), fvToList)
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Rhodium.Blamer.Heuristics (VotingHeuristic (SingleVoting))
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules (ErrorLabel (ErrorLabel))

import Helium.StaticAnalysis.Miscellaneous.ReductionTraceUtils (buildReductionTrace, getFullTrace, getLastTypeInTrace, getFirstTypeInTrace, squashTrace)
import Data.Maybe (isJust)
import Debug.Trace (trace)
import Data.List (permutations, nub)
import Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo
import Helium.StaticAnalysis.Messages.HeliumMessages (freshenRepresentation)
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances (reactClosedTypeFam)
import Helium.Utils.Utils (internalError)
import Rhodium.Core (unifyTypes, runTG)
import Control.Monad (filterM)

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
            (Constraint_Unify mf@MonoType_Fam{} t _, ErrorLabel "Residual constraint") -> do
              -- Gets the left most, most deeply nested type fam
              -- The blamed fam could be obtained differently
              blamedFam <- getFirstNestedFam cedge mf
              -- Obtain substitution of blamed type
              [MType freshBlamed] <- freshenRepresentation . (:[]) <$> getSubstTypeFull (getGroupFromEdge cedge) (MType blamedFam)
              let freshBlamed' = makeCharString freshBlamed
              -- Obtain substitution of original type
              [MType freshOg] <- freshenRepresentation . (:[]) <$> getSubstTypeFull (getGroupFromEdge cedge) (MType mf)
              -- Get potential trace.
              theTrace <- squashTrace <$> buildReductionTrace cedge freshOg
              theHint <- buildApartnessHint freshBlamed'
              case theTrace of
                [] -> do
                  permHint <- if freshBlamed == freshOg
                    then buildPermutationHint mf t
                    else return id
                  return $ Just (4, "Type family could not be reduced, no trace", constraint, eid, addProperty (TypeFamilyReduction Nothing t freshOg freshOg False) $ theHint $ permHint ci, gm)
                trc -> do
                  let Just lastType = getLastTypeInTrace trc
                  let Just firstType = getFirstTypeInTrace trc
                  permHint <- if freshBlamed == freshOg
                    then buildPermutationHint lastType t
                    else return id
                  if typeIsInType lastType pmt
                    then return $ Just (5, "Type family could not be reduced further, trace", constraint, eid, addProperty (TypeFamilyReduction (Just theTrace) t lastType firstType False) $ theHint $ permHint ci, gm)
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
                  let inferredT = if ti == 0 then t2 else t1
                  let inferredTStr = makeCharString inferredT
                  let Just lastType = getLastTypeInTrace theTrace
                  hint <- buildPermutationHint lastType inferredT
                  let Just firstType = getFirstTypeInTrace theTrace
                  if typeIsInType lastType pmt
                    then return $ Just (7, "Type family reduction type error", constraint, eid, addProperty (TypeFamilyReduction (Just theTrace) inferredTStr lastType firstType True) $ hint ci, gm)
                    else return Nothing
            _ -> return Nothing
        _                     -> return Nothing
        where
          buildPermutationHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo)) 
                                => MonoType -> MonoType -> m (ConstraintInfo -> ConstraintInfo)
          buildPermutationHint ogmf@(MonoType_Fam fn mts _) infMt = do
            let permsMt = filter (mts /=) $ permutations mts
            loopPerms permsMt
            
            where
              loopPerms (p:perms) = do
                axs <- getAxioms
                let nft = MonoType_Fam fn p Nothing
                tchs <- filterM (fmap isJust . isVertexTouchable) (nub $ fvToList nft ++ fvToList infMt :: [TyVar])
                ures <- runTG $ unifyTypes axs [] [Constraint_Unify nft infMt Nothing] tchs
                case ures of
                  Nothing -> loopPerms perms
                  Just _ -> do
                    let hint = addHint "possible fix" ("Changing " 
                                                      ++ (show . show) ogmf ++ " to " ++ (show . show) nft ++ " removes this type error")
                    return hint 
              loopPerms [] = return id
          buildPermutationHint _ _ = return id

          buildApartnessHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo)) 
                                => MonoType -> m (ConstraintInfo -> ConstraintInfo)
          buildApartnessHint mt@(MonoType_Fam fn _ _) = do
            axs <- getAxioms
            
            let mClosedAxs = getMaybeClosedAxs axs fn         

            mApartErr <- case mClosedAxs of
              Nothing -> return Nothing
              Just caxs -> snd <$> reactClosedTypeFam False False (Constraint_Unify mt (MonoType_Con "Char" Nothing) Nothing) caxs
            case mApartErr of
              Just (amt, r) -> do
                let hint = addHint "probable cause" ("type " ++ (show . show) mt ++ " is not apart from instance " ++ (show . show) amt ++ " at " ++ show r)
                return hint
              Nothing -> return $ addHint "probable cause" ((show . show) mt ++ " is not reducable. No matching instance was found")
          buildApartnessHint _ = return id

          getMaybeClosedAxs :: [Axiom ConstraintInfo] -> String -> Maybe [Axiom ConstraintInfo]
          getMaybeClosedAxs (Axiom_ClosedGroup fn1 cgaxs: _) fn2
            | fn1 == fn2 = Just cgaxs
          getMaybeClosedAxs (_:axs) fn = getMaybeClosedAxs axs fn
          getMaybeClosedAxs [] _     = Nothing

          getFirstNestedFam :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, CompareTypes m (RType ConstraintInfo))
                            => TGEdge (Constraint ConstraintInfo) -> MonoType -> m MonoType
          getFirstNestedFam cedge mf@(MonoType_Fam fn mts _) = do
            let varsInTf = filter isVar mts
            substVars <- mapM (getSubstTypeFull (getGroupFromEdge cedge) . MType) varsInTf
            -- substVarsMt is all type family applications obtained from vars. They were not reducable.
            let substVarsMt = filter isFam $ map (\(MType m) -> makeCharString m) substVars
            if null substVarsMt
              then return mf
              else getFirstNestedFam cedge $ head substVarsMt
          getFirstNestedFam _ _ = internalError "TypeFamilyHeuristics.hs" "getFirstNestedFam" "Only type families should be pattern matched!"

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