module Helium.StaticAnalysis.HeuristicsOU.ResidualHeuristics where

import Rhodium.Blamer.ResidualHeuristics
import Rhodium.Blamer.Path
import Rhodium.Core
import Rhodium.TypeGraphs.Touchables
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphReset


import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.FilterHeuristics

import Unbound.LocallyNameless hiding (from, to)
import Unbound.LocallyNameless.Fresh

import Data.Maybe
import Data.List
import qualified Data.Map.Strict as M

import Control.Monad

import Debug.Trace

typeSignatureTooGeneral :: Fresh m => VotingResidualHeuristic m Axiom TyVar RType Constraint ConstraintInfo
typeSignatureTooGeneral = SingleVotingResidual "Type signature too general" f
    where
        f (constraint, eid, ci, ogm) =
           -- error (show constraint)
            case maybeExplicitTypedDefinition ci of 
                Nothing -> return Nothing
                Just (ms, n) -> do
                    graph <- getGraph
                    let edge = getEdgeFromId graph eid
                    if isEdgeGiven edge then
                        return Nothing
                    else
                        return $ Just (2, "Type signature too general", constraint, eid, ci, gm) --error $ show (constraint, eid, ci, ms, n)
            --return Nothing
            --m (Maybe (Int, String, constraint, EdgeId, ci, GraphModifier touchable types constraint ci)))
        gm (eid, constraint, ci) g = do
            --let (Constraint_Unify m1 m2 _) = constraint
            let fvs = fv constraint :: [TyVar]
            let g' = (markTouchables (map (\v -> (v, 0)) fvs) g)
            return $ removedUnresolvedTried g'

isClassConstraint :: Constraint -> Bool
isClassConstraint (Constraint_Class _ [_] _) = True
isClassConstraint _ = False

classSubst :: (HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo, Fresh m) => Constraint -> m Constraint
classSubst (c@(Constraint_Class n [m] ci)) = do
    MType m' <- getSubstType $ MType m
    return (Constraint_Class n [m'] ci)

missingPredicate :: Fresh m => Path m Axiom TyVar RType Constraint ConstraintInfo -> VotingResidualHeuristic m Axiom TyVar RType Constraint ConstraintInfo            
missingPredicate path = SingleVotingResidual "Missing predicate" f
    where
        f (constraint, eid, ci, ogm) = 
            case constraintFromPath path of
                cc@(Constraint_Class cname [ms] _) -> 
                    case constraint of
                        Constraint_Inst m1 p2 _ -> do
                            graph <- getGraph
                            axioms <- getAxioms
                            let cedge = getEdgeFromId graph eid
                            MType ms' <- getSubstType $ MType ms
                            case ms' of 
                                MonoType_Var _ v -> do
                                    graph <- getGraph
                                    nedges1 <- getNeighbours (from cedge)
                                    nedges2 <- getNeighbours (to cedge)
                                    let anconstraints = filter (\e -> isConstraintEdge e && original e) $ nub (nedges1 ++ nedges2) 
                                    let fbEdges = filter (\e -> isConstraintEdge e && isJust (maybeFunctionBinding <$> getConstraintInfo (getConstraintFromEdge e))) $ M.elems $ edges graph
                                    let fbEdgesVars = map (\e -> (e, fv $ getConstraintFromEdge e)) fbEdges
                                    --let fbTypes <- mapM (getSubstType . MType . var) $ 
                                    let sub = map (\(v, MType t) -> (v, t)) $ graphToSubstition [] graph
                                    let fbTypes = map (\(e, vs) -> (e, map (\v -> substs sub (var v)) vs)) fbEdgesVars
                                    MType cType <- getSubstType $ MType $ var v
                                    let fbTypes' = filter ((cType `elem`) . snd) fbTypes
                                    let nconstraints = filter isEdgeGiven anconstraints
                                    if null fbTypes' then 
                                        return $ Just (1, "Ambigious type: " ++ show cc, constraint, eid, addProperty (AmbigiousClass cc) ci, gm)--error $ show ("Ambigious type", cc)
                                    else if null nconstraints then do
                                        let fbType' = getConstraintFromEdge $ fst $ head fbTypes'     
                                        return $ Just (3, "No type signature present", constraint, eid, 
                                            addProperties [RelevantFunctionBinding fbType', AddConstraintToTypeSignature Nothing cc] ci, gm)
                                    else do
                                        let tscons = head nconstraints
                                        let ts = getConstraintFromEdge tscons
                                        let redge = getEdgeFromId graph (edgeIdFromPath path)
                                        let res = concatMap getResolver $ isResolved $ edgeCategory redge
                                        let resEdges = map (getEdgeFromId graph) res
                                        
                                        return $ Just (4, "Add constraint " ++ show cc ++ " to " ++ show ts, constraint, eid, 
                                            addProperties [ClassUsages (map (\e -> (getConstraintFromEdge e, edgeId e, fromJust $ getConstraintInfo (getConstraintFromEdge e))) resEdges),AddConstraintToTypeSignature (Just (ts, edgeId tscons, fromJust $ getConstraintInfo ts)) cc] ci, gm)
                                _ -> do
                                    let inf = influences (edgeCategory cedge)
                                    let infEdges = filter (isClassConstraint . getConstraintFromEdge) $ map (getEdgeFromId graph) inf
                                    repCons <- mapM (classSubst . getConstraintFromEdge) infEdges
                                    isUsed <- or <$> mapM (\c -> isJust <$> runTG (unifyTypes axioms [cc] [c] (fv c))) repCons 
                                    if isUsed then
                                        
                                        return $ Just (4, "Missing instance: " ++ show cname ++ " " ++ show ms', constraint, eid, addProperty (MissingConcreteInstance cname ms') ci, gm)
                                    else
                                        return Nothing
                        _ -> return Nothing
                    
                _ -> return Nothing
        gm (eid, c, ci) g = do
            let edge = getEdgeFromId g eid
            ng <- convertConstraint [] True True (getGroupFromEdge edge) (getPriorityFromEdge edge) c
            return (mergeGraph g ng)


avoidTrustedResidualConstraints :: Monad m => ResidualHeuristic m axiom touchable types Constraint ConstraintInfo
avoidTrustedResidualConstraints = 
        let f (_, _, info, _) = return (trustFactor info)
        in minimalResidualEdgeFilter "Trust factor of edge" f

avoidForbiddenResidualConstraints :: Monad m => ResidualHeuristic m axiom touchable types Constraint ConstraintInfo
avoidForbiddenResidualConstraints = 
    residualEdgeFilter "Avoid forbidden constraints" f
        where 
            f (_, _, info, _) = return (not (isHighlyTrusted info))

resultsResidualEdgeFilter :: (Eq a, Monad m) => ([a] -> a) -> String -> ((constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m a) -> ResidualHeuristic m axiom touchable types constraint ci
resultsResidualEdgeFilter selector description function =
    FilterResidual description $ \es -> 
            do 
                tupledList <-    let f tuple = 
                                        do  result <- function tuple
                                            return (result, tuple)
                                in mapM f es
                let maximumResult 
                        | null tupledList = error "resultsEdgeFilter, unexpected empty list" 
                        | otherwise       = selector (map fst tupledList)
                return (map snd (filter ((maximumResult ==) . fst) tupledList))

maximalResidualEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m a) -> ResidualHeuristic m axiom touchable types constraint ci
maximalResidualEdgeFilter = resultsResidualEdgeFilter maximum

minimalResidualEdgeFilter :: (Ord a, Monad m) => String -> ((constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m a) -> ResidualHeuristic m axiom touchable types constraint ci
minimalResidualEdgeFilter = resultsResidualEdgeFilter minimum        

residualEdgeFilter :: Monad m => String -> ((constraint, EdgeId, ci, GraphModifier m axiom touchable types constraint ci) -> m Bool) -> ResidualHeuristic m axiom touchable types constraint ci
residualEdgeFilter description function = 
    FilterResidual description $ \es -> 
        do  xs <- filterM function es
            return (if null xs then es else xs)