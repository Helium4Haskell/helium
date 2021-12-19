{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
module Helium.StaticAnalysis.HeuristicsOU.ResidualHeuristics where

import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.Path
import Rhodium.Core
import Rhodium.TypeGraphs.Touchables
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphReset
import Rhodium.Solver.Rules

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.FilterHeuristics
import Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics
import Helium.StaticAnalysis.Heuristics.HeuristicsInfo
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree


import Unbound.Generics.LocallyNameless hiding (from, to, join)
import Unbound.Generics.LocallyNameless.Fresh

import Data.Maybe
import Data.List
import qualified Data.Map.Strict as M

import Control.Monad

import Debug.Trace

typeSignatureTooGeneral :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
typeSignatureTooGeneral path = SingleVoting "Type signature too general" f
    where
        f (constraint, eid, ci, ogm) 
            | labelFromPath path /= labelResidual = return Nothing
            | isTypeAnnotation ci =
                return $ if any (`elem` (fvToList constraint :: [TyVar])) (fvToList (constraintFromPath path) :: [TyVar]) then
                    Just (2, "Type signature too general", constraint, eid, ci, gm) 
                else
                    Nothing
            | otherwise = 
                case maybeExplicitTypedDefinition ci of 
                    Nothing -> return Nothing
                    Just (ms, n) -> do
                        graph <- getGraph
                        let edge = getEdgeFromId graph eid
                        let eedge = constraintFromPath path
                        return $ if Just True /= (isExplicitTypedBinding <$> getConstraintInfo constraint) || not (any (`elem` (fvToList constraint :: [TyVar])) (fvToList eedge :: [TyVar] )) then
                            Nothing
                        else
                            Just (2, "Type signature too general", constraint, eid, ci, gm)
        gm (eid, constraint, ci) g = do
                let g' = resetAll g
                let cedge = getEdgeFromId g eid
                let g'' = g'{
                        edges = M.filter (\e -> not (isConstraintEdge e) || getConstraintFromEdge cedge /= getConstraintFromEdge e) (edges g'),
                        unresolvedConstraints = [],
                        nextUnresolvedConstraints = []
                    }
                return (g'', ci)

                
isTypeAnnotation :: ConstraintInfo -> Bool
isTypeAnnotation cinfo =
   case (self . attribute . localInfo) cinfo of
      UHA_Expr Expression_Typed{} -> True
      _ -> False


classSubst :: (HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, Fresh m) => TGEdge (Constraint ConstraintInfo) -> Constraint ConstraintInfo -> m (Constraint ConstraintInfo)
classSubst edge (c@(Constraint_Class n [m] ci)) = do
    MType m' <- getSubstTypeFull (getGroupFromEdge edge) $ MType m
    return (Constraint_Class n [m'] ci)

missingPredicate :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo            
missingPredicate path = SingleVoting "Missing predicate" f
    where
        f (constraint, eid, ci, gm) = 
            case constraintFromPath path of
                cc@(Constraint_Class cname [ms] _) -> 
                    case constraint of
                        Constraint_Inst m1 p2 _ -> do
                            graph <- getGraph
                            axioms <- getAxioms
                            let cedge = getEdgeFromId graph eid
                            MType ms' <- getSubstTypeFull (getGroupFromEdge cedge) $ MType ms
                            case ms' of 
                                MonoType_Var _ v -> do
                                    --graph <- getGraph
                                    nedges1 <- getNeighbours (from cedge)
                                    nedges2 <- getNeighbours (to cedge)
                                    let anconstraints = filter (\e -> isConstraintEdge e && original e) $ nub (nedges1 ++ nedges2) 
                                    let fbEdges = filter (\e -> isConstraintEdge e && isJust (join $ maybeFunctionBinding <$> getConstraintInfo (getConstraintFromEdge e))) $ M.elems $ edges graph
                                    let fbEdgesVars = map (\e -> (e, fvToList $ getConstraintFromEdge e :: [TyVar])) fbEdges
                                   
                                    fbTypes <- mapM (\(e, vs) -> (mapM (getSubstTypeFull (getGroupFromEdge cedge) . MType . var) vs >>= (\ vs' -> return (e, vs')))) fbEdgesVars {-(e, map (\v -> substs sub (var v)) vs)) -}
                                    cType <- getSubstTypeFull (getGroupFromEdge cedge) $ MType $ var v
                                    let fbTypes' = filter ((cType `elem`) . map (MType . var) . concatMap getFreeVariables . snd) fbTypes
                                    let nconstraints = filter isEdgeGiven anconstraints
                                    if null fbTypes' then do
                                        let possibleRelevantEdges = filter (\e -> isConstraintEdge e && getPriorityFromEdge e > 1 && even (getPriorityFromEdge e) && isUnifyConstraint (getConstraintFromEdge e) && Just False == (isGADTPatternApplication <$> getConstraintInfo (getConstraintFromEdge e))) $ M.elems $ edges graph
                                        substReleventEdges <- mapM (\e -> (\(Constraint_Unify _ p _) -> getSubstTypeFull (getGroupFromEdge e) (MType p)) (getConstraintFromEdge e) >>= \v -> return (v, e)) possibleRelevantEdges -- (((\(Constraint_Inst _ p _) -> getSubstType (PType p)) getConstraintFromEdge e), e)
                                        let releventEdges = filter ((cType `elem`) . map (MType . var) . getFreeVariables . fst) substReleventEdges
                                        if null releventEdges then  do 
                                            let fconstraints = runFreshM $ getConstraintsFromPolyType p2
                                            return $ if cname `elem` map getNameFromConstraint fconstraints then
                                                Just (1, "Ambigious type: " ++ show cc, constraint, eid, addProperty (AmbigiousClass cc) ci, gm)
                                            else
                                                Nothing
                                        else do 
                                            let tscons = snd $ head releventEdges
                                            let ts = getConstraintFromEdge tscons
                                            let (Constraint_Unify m _ _) = getConstraintFromEdge tscons
                                            let instConstraint = filter ((\(Constraint_Inst m' _ _) -> m' == m) . getConstraintFromEdge) $ filter (\e -> isConstraintEdge e && isInstConstraint (getConstraintFromEdge e) && odd (getPriorityFromEdge e)) $ M.elems (edges graph)
                                            ts <- if null instConstraint then return ts else do
                                                let Constraint_Inst m1 p2 ci = getConstraintFromEdge $ head instConstraint
                                                PType p2' <- getSubstTypeFull (getGroupFromEdge cedge) (PType p2)
                                                return (Constraint_Inst m1 p2' ci)
                                            return $ if isJust (maybeExplicitTypedDefinition ci) || isPattern ci then
                                                Nothing
                                            else
                                                Just (4, "Add constraint " ++ show cc ++ " to gadt constructor " ++ show ts, constraint, eid, addProperties [GADTTypeSignature, AddConstraintToTypeSignature (Just (ts, edgeId tscons, fromJust $ getConstraintInfo ts)) cc] ci, gm)
                                    else if null nconstraints then do
                                        let fbType' = getConstraintFromEdge $ fst $ head fbTypes'
                                        return $ Just (3, "No type signature present", constraint, eid, 
                                            addProperties [RelevantFunctionBinding fbType', AddConstraintToTypeSignature Nothing cc] ci, addConstraintModifier True [0] 0 cc)
                                    else do
                                        let tscons = head nconstraints
                                        let ts = getConstraintFromEdge tscons
                                        let redge = getEdgeFromId graph (edgeIdFromPath path)
                                        let res = concatMap getResolver $ isResolved $ edgeCategory redge
                                        let resEdges = map (getEdgeFromId graph) res
                                        
                                        return $ Just (4, "Add constraint " ++ show cc ++ " to " ++ show ts, constraint, eid, 
                                            addProperties [ClassUsages (map (\e -> (getConstraintFromEdge e, edgeId e, fromJust $ getConstraintInfo (getConstraintFromEdge e))) resEdges),AddConstraintToTypeSignature (Just (ts, edgeId tscons, fromJust $ getConstraintInfo ts)) cc] ci, 
                                                addConstraintModifier True (getGroupFromEdge tscons)  (getPriorityFromEdge tscons) cc)
                                _ -> do
                                    let inf = influences (edgeCategory cedge)
                                    let infEdges = filter (isClassConstraint . getConstraintFromEdge) $ map (getEdgeFromId graph) inf
                                    repCons <- mapM (\e -> classSubst e $ getConstraintFromEdge e) infEdges
                                    isUsed <- or <$> mapM (\c -> isJust <$> runTG (unifyTypes axioms [cc] [c] (fvToList c))) repCons 
                                    return $ if isUsed then
                                        Just (4, "Missing instance: " ++ show cname ++ " " ++ show ms', constraint, eid, addProperty (MissingConcreteInstance cname ms') ci, gm)
                                    else
                                        Nothing
                        _ -> return Nothing
                    
                _ -> return Nothing

getConstraintsFromPolyType :: PolyType ConstraintInfo -> FreshM [Constraint ConstraintInfo]
getConstraintsFromPolyType (PolyType_Mono cs _) = return cs
getConstraintsFromPolyType (PolyType_Bind _ b) = (snd <$> unbind b) >>= getConstraintsFromPolyType
getConstraintsFromPolyType _ = return []

getNameFromConstraint :: Constraint ConstraintInfo -> String
getNameFromConstraint (Constraint_Class cname _ _) = cname
getNameFromConstraint _ = error "Only class constraints have a name"

addConstraintModifier :: HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo => Bool -> Groups -> Priority -> Constraint ConstraintInfo -> GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
addConstraintModifier isGiven group prior constraint (_, _, ci) graph = do
    let g' = resetAll graph
    cC <- convertConstraint [] True isGiven group prior constraint
    return (markEdgesUnresolved [0] $ mergeGraphs g' [cC], ci)