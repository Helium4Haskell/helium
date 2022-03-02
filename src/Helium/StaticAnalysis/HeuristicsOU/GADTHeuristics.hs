{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGAUGE MonoLocalBinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
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
import Rhodium.Solver.Rules

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics
import Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree

import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless

import Data.Maybe
import Data.List
import qualified Data.Map as M

import Control.Monad
import Control.Arrow
import Control.Monad.Trans.State

import Debug.Trace
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes ()
import Control.Monad.IO.Class (MonadIO)


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

modifyTopLevelTS    :: (HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, Fresh m) 
                    => MonoType 
                    -> PolyType ConstraintInfo 
                    -> TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo 
                    -> Constraint ConstraintInfo 
                    -> Constraint ConstraintInfo 
                    -> ErrorLabel 
                    -> m Bool
modifyTopLevelTS m pm graph fbc@(Constraint_Unify fbm@(MonoType_Var _ fbv _) _ _) origE origL = do
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
    (res, resG) <- runModGraph (fvToList pm) axioms gComplete
    return ((origE, origL) `notElem` map (\(ci, cons, l) -> (cons, l)) (errors res))
modifyTopLevelTS _ _ _ _ _ _ = return False 
    
    

runModGraph :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) 
            => [TyVar] 
            -> [Axiom ConstraintInfo] 
            -> TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo 
            -> m (SolveResult TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, TGGraph TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo)
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
            
            return (graphToSolveResult axioms False [] g', g')
        )
        

constructMGU :: (HasAxioms m (Axiom ConstraintInfo), Fresh m, MonadFail m, MonadIO m) =>
                TGGraph touchable types (Constraint ConstraintInfo) ci
                -> TGEdge constraint
                -> [TGEdge (Constraint ConstraintInfo)]
                -> m (Maybe (Constraint ConstraintInfo), MonoType,
                   [[Constraint ConstraintInfo]])
constructMGU graph cedge spp = do
    axioms <- getAxioms
    let groups = filter ((tail (getGroupFromEdge cedge) ==) . tail) $ nub $ map getGroupFromEdge $ filter isConstraintEdge $ M.elems $ edges graph
    let patternBranches = map (map getConstraintFromEdge . snd) $ combineGroups (length spp `div` length groups) groups spp

    let constraintToPatternMatchConstraint :: Constraint ConstraintInfo -> Constraint ConstraintInfo
        constraintToPatternMatchConstraint c = let
            Just ci = getConstraintInfo c 
            Just (_, _, Just gc) = maybePatternMatch ci
            in gc
    let patternCI = map ((\cs -> (snd $ chead cs, map fst cs)) . map (\c -> (fst $ splitEquality c, constraintToPatternMatchConstraint c))) (trace (show patternBranches) patternBranches)
    patternSub <- mapM (\(gc, vs) -> (\sub -> (map (\(v, MType mt) -> (v, mt)) <$> sub, vs)) <$> runTG (unifyTypes' (ignoreTouchables emptySolveOptions) axioms [] [gc] [])) patternCI
    let fbType = getConstraintFromEdge <$> maybeHead (filter (\e -> isConstraintEdge e && isJust (getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding)) $ M.elems $ edges graph)
    let subApply :: Maybe [(TyVar, MonoType)] -> [RType ConstraintInfo] -> Maybe ([(TyVar, MonoType)], [MonoType])
        subApply Nothing _ = Nothing
        subApply (Just sub) vs = Just (sub, map (\(MType mv@(MonoType_Var _ v _)) -> fromMaybe mv (lookup v sub)) vs)
    let subTypes = map (uncurry subApply) patternSub
    let     subToFunction :: Maybe (Constraint ConstraintInfo) -> Maybe ([(TyVar, MonoType)], [MonoType]) -> Maybe MonoType
            subToFunction (Just (Constraint_Unify _ ft _)) (Just (sub, params)) = do 
                    let (_, MonoType_Var _ res _) = functionSpine ft
                    resType <- lookup res sub
                    return (foldr (:-->:) resType params)
            subToFunction v1 v2 = Nothing
    let ftype = mapMaybe (subToFunction fbType) subTypes
    
    mgu <- mostGeneralUnifier ftype
    return (fbType, mgu, patternBranches)


unreachablePatternHeuristic :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
unreachablePatternHeuristic path = SingleVoting "Unreachable GADT pattern" f
    where 
        f (constraint, eid, ci, gm) = 
            if not (isFromGadt ci) then
                return Nothing
            else do 
                graph <- getGraph
                let cedge = getEdgeFromId graph eid
                let priority = getPriorityFromEdge cedge
                case constraint of
                    Constraint_Inst m1 (PolyType_Mono _ m2) _ 
                        | priority > 1 && even priority -> doWithoutConstraint constraint $ do
                            MType m1' <- getSubstTypeFull (getGroupFromEdge cedge) (MType m1)
                            MType m2' <- getSubstTypeFull (drop 1 $ getGroupFromEdge cedge) (MType m2)
                            let (_, patternRes) = functionSpine m1'
                            let (_, typeSigRes) = functionSpine m2'
                            axioms <- getAxioms
                            resSubs <- runTG (unifyTypes axioms [] [Constraint_Unify patternRes typeSigRes Nothing] (getFreeVariables (MType typeSigRes :: RType ConstraintInfo)))
                            if isNothing resSubs then do
                                let spp = selectPriorityPatterns graph (getPriorityFromEdge cedge)
                                if null spp then    
                                    return $ Just (1, "Unreachable pattern", constraint, eid, addProperty (UnreachablePattern m1' m2') ci, removePriorGM (getGroupFromEdge cedge))
                                else do
                                    (fbType, mgu, _) <- constructMGU graph cedge spp
                                    isMguCorrect <- maybe (return False) (\m -> modifyTopLevelTS mgu (PolyType_Mono [] mgu) graph m (constraintFromPath path) (labelFromPath path)) fbType
                                    when isMguCorrect (logMsg (show mgu ++ " would fix the problem"))
                                    let ci' | isMguCorrect = addProperty (PossibleTypeSignature  (PolyType_Mono [] mgu)) ci
                                            | otherwise = ci
                                    return $ Just (1, "Unreachable pattern", constraint, eid, addProperty (UnreachablePattern m1' m2') ci', removePriorGM (getGroupFromEdge cedge))
                            else
                                return Nothing
                    _ -> return Nothing

removePriorGM :: Monad m => Groups -> GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
removePriorGM groups (_, _, ci) graph = 
    let g' = resetAll graph
    in return (g'{
            edges = M.filter (\e -> not (isConstraintEdge e) || not (groups `isSuffixOf` getGroupFromEdge e )) (edges g'),
            unresolvedConstraints = [],
            nextUnresolvedConstraints = []
        }, ci)

missingGADTSignature :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
missingGADTSignature path = SingleVoting "Missing GADT Signature" f
    where
        f (constraint, eid, ci, gm) =
            if not (isFromGadt ci) then
                return Nothing
            else do
                graph <- getGraph
                let cedge = getEdgeFromId graph eid
                let eedge = getEdgeFromId graph (edgeIdFromPath path)
                case constraintFromPath path of
                    Constraint_Unify MonoType_Var{} MonoType_Var{} _ -> return Nothing
                    cu@(Constraint_Unify m1@MonoType_Var{} m2 _) | getPriorityFromEdge cedge == getPriorityFromEdge eedge -> 
                        case constraint of
                            Constraint_Unify (MonoType_Var _ cv1 _) (MonoType_Var _ cv2 _) _ -> do
                                let fbEdges = filter (\e -> isConstraintEdge e && isJust (getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding)) $ M.elems (edges graph)
                                let relevantFbEdges = filter (\e -> let vs :: [TyVar] = fvToList $ getConstraintFromEdge e in cv1 `elem` vs || cv2 `elem` vs) fbEdges
                                if null relevantFbEdges then
                                    return Nothing
                                else do
                                    let fbEdge = head relevantFbEdges
                                    let Constraint_Unify mv@(MonoType_Var _ v _) _ _ = getConstraintFromEdge fbEdge
                                    let tsEdges = filter (\e -> isConstraintEdge e && original e && isInstConstraint (getConstraintFromEdge e) && firstConstraintElement (getConstraintFromEdge e) == mv) $ M.elems $ edges graph
                                    if null tsEdges then do
                                        let spp = selectPriorityPatterns graph (getPriorityFromEdge eedge)
                                        if null spp then 
                                            return Nothing
                                        else do
                                            (fbType, mgu, patternBranches) <- constructMGU graph eedge spp
                                            let func = fromMaybe (error "No parent") $ parent $ localInfo $ fromMaybe (error "No constraint info") $ getConstraintInfo $ chead $ concat patternBranches
                                            let branches = map (self . attribute) $ children func-- (mapMaybe (\x -> (self . attribute) <$> (parent $ localInfo x))) $ mapMaybe getConstraintInfo $ concat patternBranches --(map (\x -> (self . attribute) <$> (parent $ localInfo x))) $ mapMaybe getConstraintInfo $ concat patternBranches)
                                            let pt = PolyType_Mono [] mgu
                                            isMguCorrect <- modifyTopLevelTS mgu pt graph (getConstraintFromEdge fbEdge) (constraintFromPath path) (labelFromPath path)
                                            let resPt   | isMguCorrect = Just pt
                                                        | otherwise = Nothing
                                            let resGm   | isMguCorrect = addTypeSignatureModifier (getConstraintFromEdge fbEdge) mgu (PolyType_Mono [] mgu)
                                                        | otherwise = addConstraintModifier True (getGroupFromEdge eedge) (getPriorityFromEdge eedge - 1) (getConstraintFromEdge eedge)
                                            return $ Just (2, "Missing type signature " ++ show mgu, constraint, eid, addProperty (MissingGADTTypeSignature resPt (fst $ sources $ fromJust $ getConstraintInfo $ getConstraintFromEdge fbEdge) branches) ci, resGm)
                                    else
                                        return Nothing
                            _ -> return  Nothing
                    _ -> return Nothing
        


escapingGADTVariableHeuristic ::  Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
escapingGADTVariableHeuristic path = SingleVoting "Escaping GADT variable" f
    where
        f (constraint, eid, ci, gm) =
            if not (isFromGadt ci) then
                return Nothing
            else
                case constraintFromPath path of
                    Constraint_Unify{} -> do
                        graph <- getGraph 
                        let cedge = getEdgeFromId graph eid
                        let eedge = getEdgeFromId graph (edgeIdFromPath path)
                        if isEdgeGiven cedge || isPattern ci then
                            return Nothing
                        else case constraintFromPath path of
                            Constraint_Unify mv@(MonoType_Var _ v _) m2 _ -> do
                                let pathConstraints = map getConstraintFromEdge $ filter isEdgeGiven $ map (getEdgeFromId graph) $ idsFromPath path
                                let scopedGivenCons = map getConstraintFromEdge $ filter (\e -> isConstraintEdge e && Just True == (isPattern <$> getConstraintInfo (getConstraintFromEdge e))) $ M.elems $ edges graph
                                MType mv' <- getSubstTypeFull (getGroupFromEdge cedge) (MType mv)
                                let fbEdges = map getConstraintFromEdge $ filter (\e -> isConstraintEdge e && isJust (getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding)) $ M.elems $ edges graph 
                                if v `elem` concatMap getFreeVariables scopedGivenCons || mv' `elem` map var (concatMap getFreeVariables scopedGivenCons)
                                        && mv `notElem` map var (concatMap (fvToList . getResultTypeFromPatternConstraint) $ filter isUnifyConstraint scopedGivenCons)         
                                    then do
                                    MType mt <- getSubstTypeFull (getGroupFromEdge cedge) $ MType $ firstConstraintElement (constraintFromPath path)
                                    let scopedGivenCons' = filter (\c -> v `elem` (fvToList c :: [TyVar]) || mv' `elem` map var (fvToList c)) scopedGivenCons
                                    return . Just $ if v `elem` concatMap fvToList fbEdges then
                                        (1, "Escaping gadt variable", constraint, eid, addProperty (EscapingExistentital (Left mt) (chead scopedGivenCons')) ci, gm)
                                    else
                                        (2, "Unifying gadt variable with type", constraint, eid, addProperties [EdgeGroupPriority (getPriorityFromEdge cedge) (getGroupFromEdge cedge), EscapingExistentital (Right (firstConstraintElement (constraintFromPath path))) (chead scopedGivenCons')] ci, gm)
                                else do
                                    ps <- map fst <$> getPossibleTypes (tail (getGroupFromEdge eedge)) (MType $ var v)
                                    if v `elem` concatMap fvToList fbEdges || any (\p -> p `elem` concatMap fvToList fbEdges) (nub $ concatMap getFreeVariables ps) then do
                                        let spp = selectPriorityPatterns graph (getPriorityFromEdge eedge)
                                        if null spp then
                                            return Nothing
                                        else do
                                            (fbType, mgu, patternBranches) <- constructMGU graph eedge spp
                                            let func = fromMaybe (error "No parent") $ parent $ localInfo $ fromMaybe (error "No constraint info") $ getConstraintInfo $ chead $ concat patternBranches
                                            let branches = map (self . attribute) $ children func
                                            let pt = PolyType_Mono [] mgu
                                            let fbEdge = chead (filter (\c -> v `elem` (fvToList c :: [TyVar]) || any (\p -> p `elem` (fvToList c :: [TyVar])) (nub $ concatMap getFreeVariables ps)) fbEdges)
                                            isMguCorrect <- modifyTopLevelTS mgu pt graph fbEdge (constraintFromPath path) (labelFromPath path)
                                            let resPt   | isMguCorrect = Just pt
                                                        | otherwise = Nothing
                                            {-let resGm   | isMguCorrect = addTypeSignatureModifier fbEdge mgu (PolyType_Mono [] mgu)
                                                        | otherwise = addConstraintModifier True (getGroupFromEdge eedge) (getPriorityFromEdge eedge - 1) (getConstraintFromEdge eedge)-}
                                            return $ Just (2, "Result of GADT unknown", constraint, eid, addProperty (MissingGADTTypeSignature resPt (fst $ sources $ fromJust $ getConstraintInfo fbEdge) branches) ci, gm )
                                    else
                                        return Nothing
                            _ -> return Nothing
                    _ -> return Nothing

getResultTypeFromPatternConstraint :: Constraint ConstraintInfo -> Maybe MonoType
getResultTypeFromPatternConstraint (Constraint_Unify _ r _) = Just $ getResultFromType r
getResultTypeFromPatternConstraint c = Nothing

getResultFromType :: MonoType -> MonoType
getResultFromType (f :-->: a) = getResultFromType a
getResultFromType m = m

addTypeSignatureModifier    :: HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo 
                            => Constraint ConstraintInfo 
                            -> MonoType 
                            -> PolyType ConstraintInfo 
                            -> GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
addTypeSignatureModifier fbc@(Constraint_Unify fbm@(MonoType_Var _ fbv _) _ _) mts pts (_, _, ci) graph = do 
    let g' = resetAll graph
    let g'' = g'{
            edges = M.filter (\e -> not (isConstraintEdge e && fbc /= getConstraintFromEdge e && fbv `elem` getFreeTopLevelVariables (getConstraintFromEdge e))) (edges g'),
            unresolvedConstraints = [],
            nextUnresolvedConstraints = []
        }
    cG <- convertConstraint [] True True [0] 0 (Constraint_Inst fbm pts Nothing)
    cW <- convertConstraint [] True False [0] 1 (Constraint_Unify fbm mts Nothing) 
    let gComplete = markEdgesUnresolved [0] $ mergeGraphs g'' [cG, cW]
    return (gComplete, ci)

addConstraintModifier :: HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo => Bool -> Groups -> Priority -> Constraint ConstraintInfo -> GraphModifier m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
addConstraintModifier isGiven group prior constraint (_, _, ci) graph = do
    let g' = resetAll graph
    cC <- convertConstraint [] True isGiven group prior constraint
    return (markEdgesUnresolved [0] $ mergeGraphs g' [cC], ci)
    
chead [] = error "unsafe chead"
chead (x:_) = x