{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGAUGE MonoLocalBinds #-}
module Helium.StaticAnalysis.HeuristicsOU.GADTHeuristics where

import Rhodium.Core
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.HeuristicsUtils
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphReset
import Rhodium.Solver.SolveOptions
import Rhodium.Solver.SolveResult
import Rhodium.Solver.Simplifier

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics
import Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless

import Data.Maybe
import Data.List
import qualified Data.Map as M

import Control.Monad
import Control.Arrow
import Control.Monad.Trans.State

import Debug.Trace


mostGeneralUnifier :: Fresh m => [MonoType] -> m MonoType
mostGeneralUnifier ms = (\(sub, m) -> substs (mapMaybe convSub sub) m) <$> (empty >>= \e -> foldM mgu e ms)
    where
        empty :: Fresh m => m ([(MonoType, MonoType)], MonoType)
        empty =  (\v -> ([], var v)) <$> fresh (integer2Name 0)
        mgu :: Fresh m => ([(MonoType, MonoType)], MonoType) -> MonoType -> m ([(MonoType, MonoType)], MonoType)
        mgu (mapping, f1 :-->: a1) (f2 :-->: a2) = do 
            (mapping', fr) <- mgu (mapping, f1) f2
            (mapping'', ar) <- mgu (mapping', a1) a2
            return (mapping'', fr :-->: ar)
        mgu (mapping, MonoType_Var _ v1) mt = case lookup (var v1) mapping  of
                Nothing -> return ((var v1, mt) : mapping, mt)
                Just mtv -> case lookup mt mapping of
                    Nothing     | mt == mtv -> return ((mt, mt) : mapping, mt)
                    Just mtv'   | mtv == mtv' -> return (mapping, mtv)
                                | otherwise -> (\v -> ((mtv, var v) : (mtv', var v) : (var v, var v) : mapping, var v)) <$> fresh (integer2Name 0) 
        mgu (mapping, m1@(MonoType_Con s1)) m2@(MonoType_Con s2) =
            case lookup m1 mapping of
                Nothing | s1 == s2 -> return (mapping, MonoType_Con s1)
                        | otherwise -> (\v -> ((m1, var v) : (m2, var v) : (var v, var v) : mapping, var v)) <$> fresh (integer2Name 0) 
                Just mv -> return (mapping, mv)
        mgu (mapping, MonoType_App f1 a1) (MonoType_App f2 a2) = do
            (mapping', fr) <- mgu (mapping, f1) f2
            (mapping'', ar) <- mgu (mapping', a1) a2
            return (mapping'', MonoType_App fr ar)
        mgu mapping v = error $ show (mapping, v)
        convSub :: (MonoType, MonoType) -> Maybe (TyVar, MonoType)
        convSub (MonoType_Var _ v, m) = Just (v, m)
        convSub _ = Nothing

selectPriorityPatterns :: TGGraph TyVar RType Constraint ConstraintInfo -> Priority -> [TGEdge Constraint]
selectPriorityPatterns graph p = filter isCorEdge $ M.elems $ edges graph
        where
            isCorEdge :: TGEdge Constraint -> Bool
            isCorEdge e | not (isConstraintEdge e) = False
                        | not (original e) = False
                        | (odd p && getPriorityFromEdge e == p - 2) || (even p && getPriorityFromEdge e == p - 1) = maybe False isJust (maybePatternMatch <$> getConstraintInfo (getConstraintFromEdge e))
                        | otherwise = False

combineGroups :: Int -> [Groups] -> [TGEdge Constraint] -> [(Groups, [TGEdge Constraint])]
combineGroups size (g:gs) constraints = (g, take size constraints) : combineGroups size gs (drop size constraints) 
combineGroups _ [] [] = []

modifyTopLevelTS :: (HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo, Fresh m) => MonoType -> PolyType -> TGGraph TyVar RType Constraint ConstraintInfo -> Constraint -> m Bool
modifyTopLevelTS m pm graph fbc@(Constraint_Unify fbm@(MonoType_Var _ fbv) _ _) = do
    let g' = resetAll graph
    let g'' = g'{
            edges = M.filter (\e -> not (isConstraintEdge e && fbc /= getConstraintFromEdge e && fbv `elem` getFreeTopLevelVariables (getConstraintFromEdge e))) (edges g'),
            unresolvedConstraints = [],
            nextUnresolvedConstraints = [],
            resolvedErrors = Nothing
        }
    cG <- convertConstraint [] True True [0] 0 (Constraint_Inst fbm pm Nothing)
    cW <- convertConstraint [] True False [0] 1 (Constraint_Unify fbm m Nothing) 
    let gComplete = markEdgesUnresolved [0] $ mergeGraphs g'' [cG, cW]
    axioms <- getAxioms
    res <- runModGraph (fv pm) axioms gComplete
    return (null (errors res))
    
    

runModGraph :: (Fresh m, HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo) => [TyVar] -> [Axiom] -> TGGraph TyVar RType Constraint ConstraintInfo -> m (SolveResult TyVar RType Constraint ConstraintInfo)
runModGraph vars axioms graph = do 
    axioms <- getAxioms
    ui <- uniqueEdge
    vi <- uniqueVertex
    oldVars <- getGivenTouchables
    runTG (
        do
            setGivenTouchables (vars ++ oldVars)
            setUniqueEdge ui
            setUniqueVertex vi
            setGraph graph
            initializeAxioms axioms
            g' <- simplifyGraph False graph
            
            return (graphToSolveResult False [] g')
        )
        


unreachablePatternHeuristic :: Fresh m => VotingHeuristic m Axiom TyVar RType Constraint ConstraintInfo
unreachablePatternHeuristic = SingleVoting "Unreachable GADT pattenr" f
    where 
        f (constraint, eid, ci) = 
            if not (isFromGadt ci) then
                return Nothing
            else do 
                graph <- getGraph
                let cedge = getEdgeFromId graph eid
                let priority = getPriorityFromEdge cedge
                case constraint of
                    Constraint_Unify m1 m2 _ 
                        | priority > 1 && even priority -> doWithoutEdge eid $ do
                            MType m1' <- getSubstType (MType m1)
                            MType m2' <- getSubstType (MType m2)
                            let (_, patternRes) = functionSpine m1'
                            let (_, typeSigRes) = functionSpine m2'
                            axioms <- getAxioms
                            resSubs <- runTG (unifyTypes axioms [] [Constraint_Unify patternRes typeSigRes Nothing] (getFreeVariables $ MType typeSigRes))
                            let (conPattern, _) = conList patternRes
                            let (conTypeSig, _) = conList typeSigRes
                            if isNothing resSubs && conPattern == conTypeSig then do
                                let spp = selectPriorityPatterns graph (getPriorityFromEdge cedge)
                                let groups = filter ((tail (getGroupFromEdge cedge) ==) . tail) $ nub $ map getGroupFromEdge $ filter isConstraintEdge $ M.elems $ edges graph
                                let patternBranches = map (map getConstraintFromEdge . snd) $ combineGroups (length spp `div` length groups) groups spp
                                let constraintToPatternMatchConstraint :: Constraint -> Constraint
                                    constraintToPatternMatchConstraint c = let
                                        Just ci = getConstraintInfo c 
                                        Just (_, _, Just gc) = maybePatternMatch ci
                                        in gc
                                let patternCI = map ((\cs -> (snd $ head cs, map fst cs)) . (map (\c -> (fst $ splitEquality c, constraintToPatternMatchConstraint c)))) patternBranches
                                patternSub <- mapM (\(gc, vs) -> ((\sub -> (map (\(v, MType mt) -> (v, mt)) <$> sub, vs)) <$> runTG (unifyTypes' (ignoreTouchables emptySolveOptions) axioms [] [gc] []))) patternCI
                                let fbType = getConstraintFromEdge <$> maybeHead (filter (\e -> isConstraintEdge e && isJust ((getConstraintInfo (getConstraintFromEdge e)) >>= maybeFunctionBinding)) $ M.elems $ edges graph)
                                let subApply :: Maybe [(TyVar, MonoType)] -> [RType] -> Maybe ([(TyVar, MonoType)], [MonoType])
                                    subApply Nothing _ = Nothing
                                    subApply (Just sub) vs = Just (sub, map (\(MType mv@(MonoType_Var _ v)) -> fromMaybe mv (lookup v sub)) vs)
                                let subTypes = map (uncurry subApply) patternSub
                                let     subToFunction :: Maybe Constraint -> Maybe ([(TyVar, MonoType)], [MonoType]) -> Maybe MonoType
                                        subToFunction (Just (Constraint_Unify _ ft _)) (Just (sub, params)) = do 
                                                let (_, MonoType_Var _ res) = functionSpine ft
                                                resType <- lookup res sub
                                                return (foldr (:-->:) resType params)
                                        subToFunction v1 v2 = Nothing
                                let ftype = mapMaybe (subToFunction fbType) subTypes
                                
                                mgu <- mostGeneralUnifier ftype
                                isMguCorrect <- maybe (return False) (modifyTopLevelTS mgu (PolyType_Mono [] mgu) graph) fbType
                                when isMguCorrect (logMsg (show mgu ++ " would fix the problem"))
                                let ci' | isMguCorrect = addProperty (PossibleTypeSignature  (PolyType_Mono [] mgu)) ci
                                        | otherwise = ci
                                return $ Just (1, "Unreachable pattern", constraint, eid, addProperty (UnreachablePattern m1' m2') ci')
                            else
                                return Nothing
                    _ -> return Nothing
