{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGAUGE MonoLocalBinds #-}
module Helium.StaticAnalysis.HeuristicsOU.GADTHeuristics where

import Rhodium.Core
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.ResidualHeuristics
import Rhodium.Blamer.HeuristicsUtils
import Rhodium.Blamer.Path
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphReset
import Rhodium.Solver.SolveOptions
import Rhodium.Solver.SolveResult
import Rhodium.Solver.Simplifier

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics
import Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless

import Data.Maybe
import Data.List
import qualified Data.Map as M

import Control.Monad
import Control.Arrow
import Control.Monad.Trans.State

import Debug.Trace


selectPriorityPatterns :: TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> Priority -> [TGEdge (Constraint ConstraintInfo)]
selectPriorityPatterns graph p = filter isCorEdge $ M.elems $ edges graph
        where
            isCorEdge :: TGEdge (Constraint ConstraintInfo) -> Bool
            isCorEdge e | not (isConstraintEdge e) = False
                        | not (original e) = False
                        | (odd p && getPriorityFromEdge e == p - 2) || (even p && getPriorityFromEdge e == p - 1) = maybe False isJust (maybePatternMatch <$> getConstraintInfo (getConstraintFromEdge e))
                        | otherwise = False

combineGroups :: Int -> [Groups] -> [TGEdge (Constraint ConstraintInfo)] -> [(Groups, [TGEdge (Constraint ConstraintInfo)])]
combineGroups size (g:gs) constraints = (g, take size constraints) : combineGroups size gs (drop size constraints) 
combineGroups _ [] [] = []

modifyTopLevelTS :: (HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, Fresh m) => MonoType -> PolyType ConstraintInfo -> TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> (Constraint ConstraintInfo) -> m Bool
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
    
    

runModGraph :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => [TyVar] -> [Axiom ConstraintInfo] -> TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> m (SolveResult TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
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
        

constructMGU graph cedge spp = do
    axioms <- getAxioms
    let groups = filter ((tail (getGroupFromEdge cedge) ==) . tail) $ nub $ map getGroupFromEdge $ filter isConstraintEdge $ M.elems $ edges graph
    let patternBranches = map (map getConstraintFromEdge . snd) $ combineGroups (length spp `div` length groups) groups spp
    let constraintToPatternMatchConstraint :: Constraint ConstraintInfo -> Constraint ConstraintInfo
        constraintToPatternMatchConstraint c = let
            Just ci = getConstraintInfo c 
            Just (_, _, Just gc) = maybePatternMatch ci
            in gc
    let patternCI = map ((\cs -> (snd $ head cs, map fst cs)) . (map (\c -> (fst $ splitEquality c, constraintToPatternMatchConstraint c)))) patternBranches
    patternSub <- mapM (\(gc, vs) -> ((\sub -> (map (\(v, MType mt) -> (v, mt)) <$> sub, vs)) <$> runTG (unifyTypes' (ignoreTouchables emptySolveOptions) axioms [] [gc] []))) patternCI
    let fbType = getConstraintFromEdge <$> maybeHead (filter (\e -> isConstraintEdge e && isJust ((getConstraintInfo (getConstraintFromEdge e)) >>= maybeFunctionBinding)) $ M.elems $ edges graph)
    let subApply :: Maybe [(TyVar, MonoType)] -> [RType ConstraintInfo] -> Maybe ([(TyVar, MonoType)], [MonoType])
        subApply Nothing _ = Nothing
        subApply (Just sub) vs = Just (sub, map (\(MType mv@(MonoType_Var _ v)) -> fromMaybe mv (lookup v sub)) vs)
    let subTypes = map (uncurry subApply) patternSub
    let     subToFunction :: Maybe (Constraint ConstraintInfo) -> Maybe ([(TyVar, MonoType)], [MonoType]) -> Maybe MonoType
            subToFunction (Just (Constraint_Unify _ ft _)) (Just (sub, params)) = do 
                    let (_, MonoType_Var _ res) = functionSpine ft
                    resType <- lookup res sub
                    return (foldr (:-->:) resType params)
            subToFunction v1 v2 = Nothing
    let ftype = mapMaybe (subToFunction fbType) subTypes
    
    mgu <- mostGeneralUnifier ftype
    return (fbType, mgu, patternBranches)


unreachablePatternHeuristic :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
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
                            resSubs <- runTG (unifyTypes axioms [] [Constraint_Unify patternRes typeSigRes Nothing] (getFreeVariables $ (MType typeSigRes :: RType ConstraintInfo)))
                            let (conPattern, _) = conList patternRes
                            let (conTypeSig, _) = conList typeSigRes
                            if isNothing resSubs && conPattern == conTypeSig then do
                                let spp = selectPriorityPatterns graph (getPriorityFromEdge cedge)
                                (fbType, mgu, _) <- constructMGU graph cedge spp
                                isMguCorrect <- maybe (return False) (modifyTopLevelTS mgu (PolyType_Mono [] mgu) graph) fbType
                                when isMguCorrect (logMsg (show mgu ++ " would fix the problem"))
                                let ci' | isMguCorrect = addProperty (PossibleTypeSignature  (PolyType_Mono [] mgu)) ci
                                        | otherwise = ci
                                return $ Just (1, "Unreachable pattern", constraint, eid, addProperty (UnreachablePattern m1' m2') ci')
                            else
                                return Nothing
                    _ -> return Nothing

missingGADTSignature :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingResidualHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
missingGADTSignature path = SingleVotingResidual "Missing GADT Signature" f
    where
        f (constraint, eid, ci, gm) = do
            graph <- getGraph
            let cedge = getEdgeFromId graph eid
            let eedge = getEdgeFromId graph (edgeIdFromPath path)
            case constraintFromPath path of
                Constraint_Unify (MonoType_Var _ _) (MonoType_Var _ _) _ -> return Nothing
                cu@(Constraint_Unify m1@(MonoType_Var _ _) m2 _) | getPriorityFromEdge cedge < getPriorityFromEdge eedge -> 
                    case constraint of
                        Constraint_Unify (MonoType_Var _ cv1) (MonoType_Var _ cv2) _ -> do
                            let fbEdges = filter (\e -> isConstraintEdge e && isJust (getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding)) $ M.elems (edges graph)
                            let relevantFbEdges = filter (\e -> let vs :: [TyVar] = fv $ getConstraintFromEdge e in cv1 `elem` vs || cv2 `elem` vs) fbEdges
                            if null relevantFbEdges then
                                return Nothing
                            else do
                                let fbEdge = head relevantFbEdges
                                let Constraint_Unify mv@(MonoType_Var _ v) _ _ = getConstraintFromEdge fbEdge
                                let tsEdges = filter (\e -> isConstraintEdge e && original e && isInstConstraint (getConstraintFromEdge e) && firstConstraintElement (getConstraintFromEdge e) == mv) $ M.elems $ edges graph
                                if null tsEdges then do
                                    let spp = selectPriorityPatterns graph (getPriorityFromEdge eedge)
                                    (fbType, mgu, patternBranches) <- constructMGU graph eedge spp
                                    let func = fromMaybe (error "No parent") $ parent $ localInfo $ fromMaybe (error "No constraint info") $ getConstraintInfo $ head $ concat patternBranches
                                    let branches = map (self . attribute) $ children func-- (mapMaybe (\x -> (self . attribute) <$> (parent $ localInfo x))) $ mapMaybe getConstraintInfo $ concat patternBranches --(map (\x -> (self . attribute) <$> (parent $ localInfo x))) $ mapMaybe getConstraintInfo $ concat patternBranches)
                                    let pt = PolyType_Mono [] mgu
                                    isMguCorrect <- modifyTopLevelTS mgu pt graph (getConstraintFromEdge fbEdge)
                                    let resPt   | isMguCorrect = Just pt
                                                | otherwise = Nothing
                                    return $ Just (2, "Missing type signature " ++ show mgu, constraint, eid, addProperty (MissingGADTTypeSignature resPt (fst $ sources $ fromJust $ getConstraintInfo $ getConstraintFromEdge fbEdge) branches) ci, gm)
                                else
                                    return Nothing
                        _ -> return Nothing
                _ -> return Nothing


escapingGADTVariableHeuristic ::  Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingResidualHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
escapingGADTVariableHeuristic path = SingleVotingResidual "Escaping GADT variable" f
    where
        f (constraint, eid, ci, gm) =
            case constraintFromPath path of
                Constraint_Unify _ _ _ -> do
                    graph <- getGraph 
                    let cedge = getEdgeFromId graph eid
                    let eedge = getEdgeFromId graph (edgeIdFromPath path)
                    if isEdgeGiven cedge || isPattern ci then
                        return Nothing
                    else do
                        let pathConstraints = map getConstraintFromEdge $ filter (\e -> isEdgeGiven e) $ map (getEdgeFromId graph) $ idsFromPath path
                        let Constraint_Unify mv@(MonoType_Var _ v) m2 _ = constraintFromPath path
                        let scopedGivenCons = map getConstraintFromEdge $ filter (\e -> isConstraintEdge e && Just True == (isPattern <$> getConstraintInfo (getConstraintFromEdge e))) $ M.elems $ edges graph
                        MType mv' <- getSubstType (MType mv)
                        let fbEdges = map getConstraintFromEdge $ filter (\e -> isConstraintEdge e && isJust (getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding)) $ M.elems $ edges graph 
                        if v `elem` concatMap getFreeVariables scopedGivenCons || mv' `elem` map var (concatMap getFreeVariables scopedGivenCons) then do
                            MType mt <- getSubstType $ MType $ firstConstraintElement (constraintFromPath path)
                            let scopedGivenCons' = filter (\c -> v `elem` (fv c :: [TyVar]) || mv' `elem` map var (fv c)) scopedGivenCons
                            if v `elem` concatMap fv fbEdges then
                                return $ Just (2, "Escaping gadt variable", constraint, eid, addProperty (EscapingExistentital (Left mt) (head scopedGivenCons')) ci, gm)
                            else
                                return $ Just (4, "Unifying gadt variable with type", constraint, eid, addProperty (EscapingExistentital (Right (firstConstraintElement (constraintFromPath path))) (head scopedGivenCons')) ci, gm)
                        else
                            if v `elem` concatMap fv fbEdges then do
                                let spp = selectPriorityPatterns graph (getPriorityFromEdge eedge)
                                (fbType, mgu, patternBranches) <- constructMGU graph eedge spp
                                let func = fromMaybe (error "No parent") $ parent $ localInfo $ fromMaybe (error "No constraint info") $ getConstraintInfo $ head $ concat patternBranches
                                let branches = map (self . attribute) $ children func
                                let pt = PolyType_Mono [] mgu
                                let fbEdge = head (filter (\c -> v `elem` (fv c :: [TyVar])) fbEdges)
                                isMguCorrect <- modifyTopLevelTS mgu pt graph fbEdge
                                let resPt   | isMguCorrect = Just pt
                                            | otherwise = Nothing
                                return $ Just (3, "Result of GADT unknown", constraint, eid, addProperty (MissingGADTTypeSignature resPt (fst $ sources $ fromJust $ getConstraintInfo fbEdge) branches) ci, gm)
                            else
                                return Nothing
                _ -> return Nothing


                {-}
                PType p2' <- getSubstType $ PType p2
                problemVariables <- mapM getSubstType $ map (MType . var) $ getFreeVariables (constraintFromPath path)
                if any (`elem` map fromMType problemVariables) (map var $ fv p2') then
                    do
                        --check if concrete type
                        -- check if coming from type signature
                        -- else, e
                        error ("Not an elem")
                else if length problemVariables == 1 && any (`elem` (fv p2 :: [TyVar])) (getFreeVariables (constraintFromPath path)) then do
                    MType mt <- getSubstType $ MType $ firstConstraintElement $ (constraintFromPath path)
                    doWithoutEdge eid $ do
                        MType mt' <- getSubstType $ MType $ firstConstraintElement $ (constraintFromPath path)
                        logMsg (show (mt, mt'))
                        return Nothing
                    --return $ Just (3, "Escaping with concrete type", constraint, eid, addProperty (EscapingExistentital (Just mt)) ci, gm)
                else
                    return Nothing
                    
            _ -> return Nothing
            -}