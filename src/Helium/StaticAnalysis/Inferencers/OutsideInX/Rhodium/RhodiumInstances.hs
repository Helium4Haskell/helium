{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances where

import Control.Monad.Trans.State
import Control.Monad

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M

import Rhodium.Core
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.TGState

import Rhodium.TypeGraphs.Touchables 

import Unbound.LocallyNameless hiding (to, from)
import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Name

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Messages.TypeErrors hiding (makeNotGeneralEnoughTypeError, makeReductionError, makeMissingConstraintTypeError, makeUnresolvedOverloadingError)
import Helium.StaticAnalysis.Messages.Messages
import Helium.Syntax.UHA_Range
import Helium.Syntax.UHA_Syntax

import Rhodium.Blamer.HeuristicProperties

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper

import Debug.Trace

instance FreshVariable FreshM TyVar where
    freshVariable = error "try not using fresh" -- fresh (string2Name "a")

instance (Fresh m, Monad m) => FreshVariable m TyVar where
    -- freshVariable :: m a
    freshVariable = error "try not using fresh" -- fresh (string2Name "a")

instance (CompareTypes m RType, IsTouchable m TyVar, HasAxioms m Axiom, IsTouchable m TyVar, Fresh m, Monad m) => CanCanon m TyVar RType Constraint where 
    -- canon :: Bool -> constraint -> m (Maybe ([touchable], [(touchable, types)], constraint))
    canon isGiven c = do 
        axs <- getAxioms
        canon' axs c 
            where
                canon' :: [Axiom] -> Constraint -> m (RuleResult ([TyVar], [(TyVar, RType)], [Constraint]))
                canon' axs (Constraint_Unify m1 m2 _) = do
                  ig <- greaterType (MType m1) (MType m2)
                  if ig then 
                        return $ Applied ([], [], [Constraint_Unify m2 m1 Nothing])
                  else
                    case (m1, m2) of 
                        --_ | m1 > m2 -> return $ Applied ([], [], [Constraint_Unify m2 m1])
                        (MonoType_Con "[]", MonoType_Con "[]") -> return (Applied ([], [], []))
                        --(MonoType_Con "[]", MonoType_App _ _) -> error (show m2)
                        (MonoType_Con n1, MonoType_Con n2)
                            | n1 == n2 -> return $ Applied ([], [], [])
                            | otherwise -> return (Error labelIncorrectConstructors)
                        (MonoType_Con _, MonoType_App _ _) -> return (Error labelIncorrectConstructors)
                        (MonoType_App _ _, MonoType_Con _) -> return (Error labelIncorrectConstructors)
                        (f1 :-->: a1, f2 :-->: a2) -> return $ Applied ([], [], [Constraint_Unify f1 f2 Nothing, Constraint_Unify a1 a2 Nothing])
                        (MonoType_App f1 a1, MonoType_App f2 a2) -> return $ Applied ([], [], [Constraint_Unify f1 f2 Nothing, Constraint_Unify a1 a2 Nothing])
                        (MonoType_Var _ v1, MonoType_Var _ v2) 
                            | v1 == v2 -> return $ Applied ([], [], [])
                            | otherwise -> do
                                tch1 <- isVertexTouchable v1
                                tch2 <- isVertexTouchable v2
                                case (isJust tch1, isJust tch2) of
                                    (True, True) -> do 
                                        isGreater <- greaterTouchable v1 v2
                                        if isGreater then 
                                            return $ Applied ([], [], [Constraint_Unify m2 m1 Nothing]) 
                                        else return NotApplicable
                                    --(False, True) -> return $ Applied ([], [], [Constraint_Unify m2 m1])
                                    _ -> return NotApplicable
                        (MonoType_Var _ v, _)
                            | v `elem` (fv m2 :: [TyVar]), isFamilyFree m2 -> return (Error labelInfiniteType)
                            | isFamilyFree m2 -> return NotApplicable
                            | otherwise -> case m2 of
                                MonoType_Con _    -> return NotApplicable
                                MonoType_App c a  -> do (a2, con1, vars1) <- unfamily a
                                                        (c2, con2, vars2) <- unfamily c
                                                        
                                                        return $ Applied ([], [], Constraint_Unify (var v) (MonoType_App c2 a2) Nothing : con1 ++ con2)
                                _ -> {-do 
                                    gt <- MType m1 `greaterType` MType m2
                                    if gt then 
                                        return Applied ([], [], [Constraint_Unify m2 m1])
                                    else-}
                                        return NotApplicable
                        (MonoType_Con _, MonoType_Var _ _) -> return $ Applied ([], [], [Constraint_Unify m2 m1 Nothing])
                        (MonoType_Fam f1 ts1, MonoType_Fam f2 ts2)   
                            | f1 == f2, isInjective axs f1, length ts1 == length ts2 -> return $ Applied ([], [], zipWith (\t1 t2 -> Constraint_Unify t1 t2 Nothing) ts1 ts2)
                            | f1 == f2, isInjective axs f1, length ts1 /= length ts2 -> return $ Error $ ErrorLabel $ "Different Number of arguments for " ++ show ts1 ++ " and " ++ show ts2
                            | f1 == f2, length ts1 == 0 && length ts2 == 0 -> return $ Applied ([], [], [])
                            | f1 == f2, length ts1 == length ts2 -> return NotApplicable  
                            | otherwise -> error $ show (f1, f2, isInjective axs f1, axs)
                        (MonoType_Fam f ts, _)
                            | any (not . isFamilyFree) ts -> 
                                do
                                    (ts2, cons, vars) <- unfamilys ts
                                    return (Applied (vars, [], Constraint_Unify (MonoType_Fam f ts2) m2 Nothing : cons))
                        (_, _)
                            | m1 == m2, isFamilyFree m1, isFamilyFree m2 -> return $ Applied ([], [], [])
                            | otherwise -> do
                                    {-gt <- MType m1 `greaterType` MType m2
                                    if gt then 
                                        return $ Applied ([], [], [Constraint_Unify m2 m1])
                                    else -}
                                        return NotApplicable
                canon' axs (Constraint_Inst m (PolyType_Mono cs pm) _) = return $ Applied ([], [], Constraint_Unify m pm Nothing : cs)                                  
                {-canon' axs (Constraint_Inst (MonoType_Var v) p)  =
                    let nfP = nf p
                     in if nfP `aeq` p then return NotApplicable
                                       else return $ Applied ([], [], [Constraint_Inst (MonoType_Var v) nfP])-}
                canon' axs (Constraint_Inst m p _) = do
                    (vs, c,t) <- instantiate p True
                    return $ Applied (vs, [], Constraint_Unify m t Nothing : c)
                canon' axs (Constraint_Class _ _ _) = return NotApplicable
                canon' axs c = error $ "Unknown canon constraint: " ++ show c


instantiate :: Fresh m => PolyType -> Bool -> m ([TyVar], [Constraint], MonoType)
instantiate (PolyType_Bind s b) tch = do
    (v,i) <- unbind b
    (vs, c,t) <- instantiate i tch
    
    let t' = fixVariableMapping s v t
    if tch then 
            return (v : vs, c, t')
    else 
            return ([], c, t')
instantiate (PolyType_Mono cs m) _tch = return ([], cs,m)

fixVariableMapping :: String -> TyVar -> MonoType -> MonoType
fixVariableMapping s v (MonoType_Var ms v') | v == v' = case ms of
                                                        Just m -> if m == s then (MonoType_Var ms v') else error "Conflicing variables"
                                                        Nothing -> (MonoType_Var (Just s) v')
                                        | otherwise = MonoType_Var ms v'
fixVariableMapping s v m@(MonoType_Con _) = m
fixVariableMapping s v m@(MonoType_App f a) = MonoType_App (fixVariableMapping s v f) (fixVariableMapping s v a)
fixVariableMapping s v m@(MonoType_Fam f ms) = MonoType_Fam f (map (fixVariableMapping s v) ms)



instance (HasGraph m touchable types constraint ci, CompareTypes m RType, IsTouchable m TyVar, Fresh m, Monad m) => CanInteract m TyVar RType Constraint ConstraintInfo where
    --interact :: Bool -> constraint -> constraint -> m (RuleResult [constraint])
    interact isGiven c1 c2
        | c1 == c2 = return $ Applied [c1]
    interact isGiven c1@(Constraint_Unify (MonoType_Var _ v1) m1 _) c2@(Constraint_Unify t2@(MonoType_Fam f vs2) m2 _)
        | isFamilyFree m1, all isFamilyFree vs2, v1 `elem` (fv t2 :: [TyVar]) || v1 `elem` (fv m2 :: [TyVar]), isFamilyFree m2 =
                return $ Applied [c1, Constraint_Unify (subst v1 m1 t2) (subst v1 m1 m2) Nothing]
    interact isGiven c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | v1 == v2, isFamilyFree m1, isFamilyFree m2 = do
            ig <- greaterType (MType mv1) (MType m1)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify m1 m2 Nothing]
        | v1 `elem` (fv m2 :: [TyVar]), isFamilyFree m1, isFamilyFree m2 = do 
            ig <- greaterType (MType mv1) (MType m1)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify (var v2) (subst v1 m1 m2) Nothing]
    interact isGiven c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Class n ms2 _)
        | v1 `elem` (fv ms2 :: [TyVar]), all isFamilyFree ms2 = do 
            ig <- greaterType (MType mv1) (MType m1)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Class n (substs [(v1, m1)] ms2) Nothing]
    interact isGiven c1@(Constraint_Class _ _ _) c2@(Constraint_Class _ _ _) 
        | c1 == c2 = return $ Applied [c1]
    interact isGiven c1 c2 = return NotApplicable

instance (CompareTypes m RType, HasAxioms m Axiom, Fresh m) => CanSimplify m TyVar RType Constraint ConstraintInfo where
    simplify c1 c2 
        | c1 == c2 = return $ Applied []
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | mv1 == m1 || mv2 == m2 = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Unify m1 mv1@(MonoType_Var _ v1) _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | mv1 == m1 || mv2 == m2 = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Class _ _ _) c2@(Constraint_Class _ _ _) 
        | c1 == c2 = return $ Applied []
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Class _ ms _) 
        | v1 `elem` (fv ms :: [TyVar]), isFamilyFree m1, all isFamilyFree ms = do
            gt <- greaterType (MType mv1) (MType m1)
            if gt then 
                return NotApplicable
            else
                return $ Applied [subst v1 m1 c2]
    simplify c1 c2 = return NotApplicable
    {-getSimplificationCandidates edge graph = let
        v1 = from edge
        v2 = to edge
        ns = nub $ getNeighbours graph v1 ++ getNeighbours graph v2
        in return ns-}

loopAxioms :: Monad m => (Axiom -> m (RuleResult a)) -> [Axiom] -> m (RuleResult a)
loopAxioms f [] = return NotApplicable
loopAxioms f (x:xs) = do
    res <- f x
    if res == NotApplicable then
        loopAxioms f xs
    else 
        return res

isInjective :: [Axiom] -> String -> Bool
isInjective axioms s = any isInjective' axioms
    where 
        isInjective' (Axiom_Injective n) = n == s
        isInjective' _ = False

instance (HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo, HasAxioms m Axiom, Fresh m) => CanTopLevelReact m Axiom TyVar RType Constraint where
    topLevelReact isGiven c@(Constraint_Class n cs _) = getAxioms >>= loopAxioms topLevelReact'
        where
            topLevelReact' ax@(Axiom_Class b) = do
                (aes, (ctx, cls, args)) <- unbind b
                if cls == n then do
                    let bes = fv ax :: [TyVar]
                    res <- runTG $ unifyTypes [] [] (zipWith (\c a -> Constraint_Unify c a (Nothing :: Maybe ConstraintInfo)) cs args) (aes \\ bes)
                    case res of
                      Just s -> return $ Applied ([], substs (convertSubstitution s) ctx)
                      _  -> return NotApplicable
                else
                    return NotApplicable
            topLevelReact' _ = return NotApplicable
    topLevelReact isGiven c@(Constraint_Unify (MonoType_Fam f ms) t _) = getAxioms >>= loopAxioms topLevelReact' 
        where
            topLevelReact' ax@(Axiom_Unify b) | all isFamilyFree ms, isFamilyFree t =
                do
                    (aes, (lhs, rhs)) <- unbind b
                    case lhs of
                        MonoType_Fam lF lMs | f == lF -> do
                            res <- runTG $ unifyTypes [] [] (zipWith (\m l -> Constraint_Unify m l (Nothing :: Maybe ConstraintInfo)) ms lMs) (aes \\ (fv ax :: [TyVar]))
                            case res of
                                (Just s) -> return $ Applied (if isGiven then [] else fv t, [Constraint_Unify (substs (convertSubstitution s) rhs) t Nothing])
                                _ -> return NotApplicable
                        _ -> return NotApplicable
            topLevelReact' _ = return NotApplicable
    topLevelReact isGiven constraint = return NotApplicable

convertSubstitution :: [(TyVar, RType)] -> [(TyVar, MonoType)]
convertSubstitution = map (\(t, MType m) -> (t, m))

instance (IsTouchable m TyVar, Monad m, UniqueEdge m, UniqueVertex m, UniqueGroup m, Fresh m, HasGraph m TyVar RType Constraint ConstraintInfo) => CanConvertType m TyVar RType Constraint ConstraintInfo where
    convertType isOriginal groups priority (MType m) = do 
            mv <- getVertexFromGraph (MType m)
            g <- getGraph
            if isJust mv then
                return (emptyTGGraph, fromJust mv)
            else
               convertTypeM m
        where
            convertTypeM (MonoType_Con n) = do
                v <- uniqueVertex
                return (singletonGraph v TGConstant{
                    constant = n
                }, v)
            convertTypeM (MonoType_Var s mv) = do
                v <- uniqueVertex
                graph <- getGraph
                isTch <- isVertexTouchable mv
                return  (singletonGraph v TGVariable{
                    variable = mv,
                    representation = maybe [] (:[]) s,
                    isTouchable = isTch
                }, v)
            convertTypeM m@(MonoType_App f a) = do
                v <- uniqueVertex
                (fg, fv) <- convertType isOriginal groups priority (MType f)
                (ag, av) <- convertType isOriginal groups priority (MType a)
                let vg = singletonGraph v TGApplication{
                        typeRep = MType m
                    }
                ei1 <- uniqueEdge
                let te1 = typeEdge ei1 0 isOriginal v fv
                ei2 <- uniqueEdge
                let te2 = typeEdge ei2 1 isOriginal v av
                let g1 = mergeGraphsWithEdges False [te1] vg fg 
                let g2 = mergeGraphsWithEdges False [te2] ag fg
                return (mergeGraph g1 g2, v)
            convertTypeM m@(MonoType_Fam s ms) = do
                v <- uniqueVertex 
                ms' <- mapM (convertType isOriginal groups priority . MType) ms
                let vg = singletonGraph v TGApplication{
                    typeRep = MType m
                }
                edgeIds <- replicateM (length ms) uniqueEdge
                let typeEdges = zipWith3 (\eid (_, vc) i -> typeEdge eid i isOriginal v vc) 
                                    edgeIds ms' [0..]
                return (foldr (\((ng, _), te) og -> 
                    mergeGraphsWithEdges False [te] og ng
                    ) vg (zip ms' typeEdges), v)
    convertType isOriginal groups priority (PType pt) = convertTypeP' pt
        where
            convertTypeP' :: PolyType ->  m (TGGraph TyVar RType Constraint ConstraintInfo, VertexId) 
            convertTypeP' (PolyType_Mono cs m) = do
                (m', v) <- convertType isOriginal groups priority (MType m)
                cs' <- mapM (convertConstraint [] isOriginal False groups priority) cs
                if null cs' then 
                    return (m',v)
                else 
                    let 
                        mg = insertGraphs m' cs'
                    in return (mg, fromMaybe v (M.lookup (MType m) (typeMapping mg)))
            convertTypeP' pb@(PolyType_Bind s b) = do
                v <- uniqueVertex
                f <- fresh (integer2Name 0)
                let vg = singletonGraph v TGScopedVariable{
                        typeRep = PType pb,
                        variable = f
                    }
                return (vg, v)
                {-}
                return ()
                (t, p) <- unbind b
                v <- uniqueVertex
                let vg = singletonGraph v TGScopedVariable{
                        typeRep = PType p,
                        variable = t
                    }
                (pg, pv') <- convertType isOriginal (PType p)
                ei <- uniqueEdge
                let edge = typeEdge ei 0 isOriginal v pv'
                return (mergeGraphsWithEdges False [edge] vg pg, v)
                -}



                

instance (IsTouchable m TyVar, HasGraph m TyVar RType Constraint ConstraintInfo, Fresh m, Monad m, UniqueVertex m, UniqueGroup m, UniqueEdge m) => CanConvertConstraint m TyVar RType Constraint ConstraintInfo where
    -- convertConstraint :: constraint -> m (TGGraph touchable constraint types)
    convertConstraint basedOn isOriginal isGiven groups priority c@(Constraint_Unify m1 m2 _) = do
        t1@(v1Node, v1) <- convertType isOriginal groups priority (MType m1)
        t2@(v2Node, v2) <- convertType isOriginal groups priority (MType m2)
        edgeIndex <- uniqueEdge
        let edge = constraintEdge edgeIndex basedOn c isOriginal isGiven groups priority v1 v2
        return (mergeGraphsWithEdges False [edge] v1Node v2Node)
    convertConstraint basedOn isOriginal isGiven groups priority c@(Constraint_Class s ms _) = do
        ms' <- mapM (convertType isOriginal groups priority . MType) ms
        vDead <- uniqueVertex
        let deadNode = singletonGraph vDead TGDeadNode
        vConstraintApplication <- uniqueVertex
        let constraintApplication = singletonGraph vConstraintApplication TGConstraintApplication
        edgeIds <- replicateM (length ms) uniqueEdge
        let typeEdges = zipWith3 (\eid (_, v) i -> typeEdge eid i isOriginal vConstraintApplication v) 
                            edgeIds ms' [0..]
        constraintId <- uniqueEdge
        let cEdge = constraintEdge constraintId basedOn c isOriginal isGiven groups priority vDead vConstraintApplication
        let bGraph = mergeGraphsWithEdges False [cEdge] deadNode constraintApplication
        
        return $ foldr (\((ng, _), te) og -> 
                mergeGraphsWithEdges False [te] og ng
            ) bGraph (zip ms' typeEdges)
    convertConstraint basedOn isOriginal isGiven groups priority c@(Constraint_Inst m p _) = do
        (m', v1) <- convertType isOriginal groups priority (MType m)
        (p', v2) <- convertType isOriginal groups priority (PType p)
        edgeIndex <- uniqueEdge
        let edge = constraintEdge edgeIndex basedOn c isOriginal isGiven groups priority v1 v2
        return (mergeGraphsWithEdges False [edge] m' p')
    convertConstraint basedOn isOriginal False groups priority c@(Constraint_Exists b _) = do
        (vars, (given, wanted)) <- unbind b
        ug <- uniqueGroup
        given' <- mapM (convertConstraint basedOn isOriginal True (ug : groups) (priority + 1)) given
        setGivenTouchables (concatMap getFreeVariables given)
        wanted' <- mapM (convertConstraint basedOn isOriginal False (ug : groups) (priority + 2)) wanted
        return $ markTouchables (map (\v -> (v, priority + 2)) vars) (insertGraphs emptyTGGraph (given' ++ wanted'))
        --error $ show (vars, given, wanted)

instance IsEquality RType Constraint TyVar where
    -- isEquality :: constraint -> Bool
    isEquality (Constraint_Unify _ _ _) = True
    isEquality _    = False
    -- splitEquality :: constraint -> (types, types)
    splitEquality (Constraint_Unify m1 m2 _) = (MType m1, MType m2)
    allowInSubstitution (Constraint_Unify m1 m2 _) = isFamilyFree m1 && isFamilyFree m2
    allowInSubstitution _ = False


instance CanCompareTouchable TyVar RType where
    compareTouchable tyvar (MType v) = var tyvar == v
    compareTouchable tyvar (PType v) = var tyvar == v
    convertTouchable v = MType (var v) 
    applySubstitution sub (MType m) = MType $ substs (map (\(v, MType m) -> (v, m)) sub) m 
    applySubstitution sub (PType p) = PType $ substs (map (\(v, MType m) -> (v, m)) sub) p
    extractTouchable (MType (MonoType_Var _ v)) = Just v
    extractTouchable _ = Nothing

instance ConstraintSymbol Constraint where
    showConstraintSymbol (Constraint_Unify _ _ _) = "~"
    showConstraintSymbol (Constraint_Class s _ _) = "$" ++ s
    showConstraintSymbol (Constraint_Inst _ _ _) = ">"

instance ConvertConstructor RType where
    convertConstructor s = MType (MonoType_Con s)

instance (Monad m, IsTouchable m TyVar) => CompareTypes m RType where
    greaterType (MType (MonoType_Var _ v1)) (MType (MonoType_Var _ v2)) = greaterTouchable v1 v2
    greaterType m1 m2 = return $ m1 > m2

getTLVariableFromMonoType :: MonoType -> [TyVar]
getTLVariableFromMonoType (MonoType_Var _ v) = [v]
getTLVariableFromMonoType _ = []

instance FreeVariables Constraint TyVar where
    getFreeVariables = fv
    getFreeTopLevelVariables (Constraint_Unify m1 m2 _) = getTLVariableFromMonoType m1 ++ getTLVariableFromMonoType m2
    getFreeTopLevelVariables (Constraint_Inst m1 _ _) = getTLVariableFromMonoType m1
    getFreeTopLevelVariables c = error (show c)

instance FreeVariables RType TyVar where
    getFreeVariables (MType m) = fv m
    getFreeVariables (PType p) = fv p

instance HasConstraintInfo Constraint ConstraintInfo where
    getConstraintInfo (Constraint_Unify _ _ ci) = ci
    getConstraintInfo (Constraint_Inst _ _ ci) = ci
    getConstraintInfo (Constraint_Exists _ ci) = ci
    getConstraintInfo (Constraint_Class _ _ ci) = ci
    getConstraintInfo c = error ("No constraint info for " ++ show c)
    setConstraintInfo ci (Constraint_Unify m1 m2 _) = Constraint_Unify m1 m2 (Just ci)

firstConstraintElement :: Constraint -> MonoType
firstConstraintElement (Constraint_Unify m1 _ _) = m1
firstConstraintElement (Constraint_Inst m1 _ _) = m1

instance (Fresh m, HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo) => TypeErrorInfo m Constraint ConstraintInfo where
    createTypeError li constraint ci = maybe nError (return . const ci) (errorMessage ci)
        where
            nError 
                | li == labelIncorrectConstructors && isJust (maybeUnreachablePattern ci) =
                    do
                        let Just (expected, function) = maybeUnreachablePattern ci
                        let Just tsLoc = maybeTypeSignatureLocation ci
                        return ci{
                            errorMessage = Just $ makeUnreachablePatternError (fst $ sources ci) tsLoc expected function (maybePossibleTypeSignature ci)
                        }
                        --error $ show (expected, function)
                | li == labelIncorrectConstructors || li == labelInfiniteType = 
                    do
                        te <- makeUnificationTypeError constraint ci
                        return ci{
                            errorMessage = Just te
                        }
                | li == labelResidual && isJust (maybeMissingConcreteInstance ci) =
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                axioms <- getAxioms
                                MType m1' <- getSubstType (MType m1)
                                let Just m = maybeMissingConcreteInstance ci
                                    source = fst (sources ci)
                                    extra  = (m1', Just p2)
                                return ci{
                                            errorMessage = Just $ makeReductionError source Nothing extra axioms m 
                                        }
                | li == labelResidual && isJust (maybeAmbigiousClass ci) = 
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                let Just cc = maybeAmbigiousClass ci
                                PType scheme1 <- getSubstType (PType p2)
                                MType scheme2 <- getSubstType (MType m1)
                                let Just classConstraint = maybeAmbigiousClass ci
                                return ci{
                                    errorMessage = Just $ makeUnresolvedOverloadingError (fst $ sources ci) classConstraint (scheme1, scheme2)
                                }
                | li == labelResidual && isJust (maybeAddConstraintToTypeSignature ci) =
                        case constraint of
                            Constraint_Inst m1 p2 _ -> do
                                let Just (m, cc) = maybeAddConstraintToTypeSignature ci
                                case m of
                                    Nothing -> do
                                        axioms <- getAxioms
                                        MType m1' <- getSubstType (MType m1)
                                        PType p2' <- getSubstType (PType $ addConstraint cc p2)
                                        let fbType = fromMaybe (error "No relevant function binding present") (maybeRelevantFunctionBinding ci)
                                        let Just fbci = getConstraintInfo fbType
                                        let fb = firstConstraintElement fbType
                                        --let Constraint_Unify fb _ (Just fbci) = error $ show fbType
                                        let source = fst (sources fbci)
                                        MType fb' <- getSubstType $ MType fb
                                        let extra = (fb', Nothing)
                                        let Constraint_Class nc [mt] _ = cc
                                        return ci{
                                            errorMessage = Just $ makeReductionError source (Just $ fst (sources ci)) extra axioms (nc, mt)
                                        } 
                                    Just (cts, eid, cits) -> do
                                        let err    = error "unknown type signature location"
                                        let range   = fromMaybe err (maybeTypeSignatureLocation ci)
                                        let mSource = if isExprTyped ci then Nothing else Just (fst $ sources ci)
                                        MType m1' <- getSubstType (MType m1)
                                        PType p2' <- getSubstType (PType $ addConstraint cc p2)
                                        let source = fst (sources ci)
                                        let extra = (m1', Just p2')
                                        let Constraint_Class nc [mt] _ = cc
                                        axioms <- getAxioms
                                        let Just usages = maybeClassUsages ci
                                        return ci{
                                            errorMessage = Just $ makeMissingConstraintTypeError range mSource m1' (True, cc) (map (fst . sources . (\(_, _, c) -> c)) usages)
                                        }
                | li == labelResidual = 
                        case constraint of
                            Constraint_Inst m1 scheme2 _ -> do
                                MType scheme1 <- getSubstType (MType m1)
                                graph <- getGraph
                                
                                let 
                                    range   = fromMaybe err (maybeTypeSignatureLocation ci)
                                    source  = uncurry fromMaybe (sources ci)
                                    err     = noRange -- error "unknown original type scheme"
                                    
                                    te = makeNotGeneralEnoughTypeError (isExprTyped ci) range source scheme1 scheme2
                                return ci{
                                    errorMessage = Just te
                                }
                            c -> return ci{
                                    errorMessage = Just $ TypeError [] [MessageOneLiner (MessageString ("Unknown residual constraint: " ++ show c))] [] []
                                }
                | isPrefixOf "Touchable touched:" (show li)   =
                    return ci{
                            errorMessage = Just $ TypeError [] [MessageOneLiner (MessageString ("Unknown residual constraint: " ++ show constraint))] [] []
                            }
                | otherwise = error ("Unknown error label: " ++ show li)


makeUnreachablePatternError :: UHA_Source -> Range -> MonoType -> MonoType -> Maybe PolyType -> TypeError
makeUnreachablePatternError source functionRange expected inferred possibleTS= 
    let 
        range = rangeOfSource source
        oneliner = MessageOneLiner (MessageString "Pattern is not accessible")
        table = [
                    "Pattern" <:> MessageOneLineTree (oneLinerSource source)
                ,   "constructor type" >:> MessageString (show expected)
                ,   "defined at" >:> MessageRange functionRange
                ,   "inferred type" >:> MessageString (show inferred)
            ]
        hints = ("hint", MessageString "change the type signature, remove the branch or change the branch")
                :  
                [
                    ("possible type signature", MessageString (show ps)) | Just ps <- [possibleTS]
                ]
    in TypeError [range] [oneliner] table hints

makeNotGeneralEnoughTypeError :: Bool -> Range -> UHA_Source -> MonoType -> PolyType -> TypeError
makeNotGeneralEnoughTypeError isAnnotation range source tpscheme1 tpscheme2 =
    let 
        ts1      = show tpscheme1
        ts2      = show tpscheme2
        special  = if isAnnotation then "Type annotation" else "Type signature"
        oneliner = MessageOneLiner (MessageString (special ++ " is too general"))
        descr    = if isAnnotation then "expression" else "function"
        table    = [ descr           <:> MessageOneLineTree (oneLinerSource source)
                    , "declared type" >:> MessageString ts2
                    , "inferred type" >:> MessageString ts1
                    ]
        hints    = [ ("hint", MessageString "try removing the type signature") | not (null (fv tpscheme1 :: [TyVar])) ] 
    in TypeError [range] [oneliner] table hints


makeUnificationTypeError :: (Fresh m, HasTypeGraph m Axiom TyVar RType Constraint ConstraintInfo) => Constraint -> ConstraintInfo -> m TypeError
makeUnificationTypeError constraint info =
    do
    let (source, term) = sources info
        range    = maybe (rangeOfSource source) rangeOfSource term
        oneliner = MessageOneLiner (MessageString ("Type error in " ++ location info))
        (t1, t2) = case constraint of
            Constraint_Unify t1 t2 _ -> (MType t1, MType t2)
            Constraint_Inst t1 t2 _ -> (MType t1, PType t2)
    --let    Constraint_Unify t1 t2 _ = constraint
   
    msgtp1   <- getSubstType t1
    msgtp2   <- getSubstType t2
    let (reason1, reason2)   
            | isJust (maybeSkolemizedTypeScheme info) = ("inferred type", "declared type")
            | isFolkloreConstraint info               = ("type"         , "expected type")
            | otherwise                                = ("type"         , "does not match")
        table = [ s <:> MessageOneLineTree (oneLinerSource source') | (s, source') <- convertSources (sources info)] 
                ++
                [ reason1 >:> MessageString (show msgtp1)
                , reason2 >:> MessageString (show msgtp2)
                ]
        hints      = [ hint | WithHint hint <- properties info ]
    return $ TypeError [range] [oneliner] table hints

makeReductionError :: UHA_Source -> Maybe UHA_Source -> (MonoType, Maybe PolyType) -> [Axiom] -> (String, MonoType) -> TypeError
makeReductionError source usage extra axioms (className, predicateTp) =
    let location = "function"
        message  = [ MessageOneLiner $ MessageString $ "Type error in overloaded " ++ show location ]
        tab1     = case extra of 
                        (scheme, Just tp) -> -- overloaded function
                            [ "function" <:> MessageOneLineTree (oneLinerSource source)
                            , "type"     >:> MessageString (show tp)
                            , "used as"  >:> MessageString (show scheme)
                            ]
                        (scheme, Nothing) ->
                            [ 
                                    "function" <:> MessageOneLineTree (oneLinerSource source)
                                ,   "inferred type"  >:> MessageString (show scheme)
                                   
                            ] ++ maybe [] (\u -> ["arising from" >:> MessageOneLineTree (oneLinerSource u)]) usage
        tab2     =  [ "problem"  <:> MessageCompose [ MessageString (show predicateTp)
                                                    , MessageString (" is not an instance of class "++className)
                                                    ]
                    ]
    in TypeError [rangeOfSource source] message (tab1 ++ tab2) [case snd extra of
        Just _ -> ("hint", MessageString hint)
        Nothing -> ("hint", MessageString "add a type signature to the function")
        ]
    where  
        hint :: String
        hint = case valids of
                  []  -> "there are no valid instances of "++className
                  [x] -> "valid instance of "++className++" is "++show x
                  _   -> "valid instances of "++className++" are "++prettyAndList (nub valids)
             
        valids :: [String]
        valids = let    
                        tps              = mapMaybe (instances className) axioms
                        (tuples, others) =  let     p (MonoType_Con s) = isTupleConstructor s
                                                    p _        = False
                                            in partition (p . fst . leftSpine) tps
                 in if length tuples > 4 -- magic number!
                      then map (show) others ++ ["tuples"]
                      else map (show) tps

        instances :: String -> Axiom -> Maybe MonoType
        instances s (Axiom_Class b) = let (vars, (cond, cn, [mt])) = runFreshM $ unbind b
                                        in  if s == cn then 
                                                Just mt
                                            else
                                                Nothing 
        instances s _ = Nothing
                    
makeMissingConstraintTypeError :: Range -> Maybe UHA_Source -> MonoType -> (Bool, Constraint) -> [UHA_Source] -> TypeError
makeMissingConstraintTypeError range mSource scheme (original, predicate) arisingFrom =
    let special  = if isJust mSource then "signature" else "annotation"
        oneliner = MessageOneLiner (MessageString ("Missing class constraint in type "++special))
        table    = maybe [] (\source -> ["function" <:> MessageOneLineTree (oneLinerSource source)]) mSource ++
                    [ (isJust mSource, MessageString "declared type", MessageString $ show scheme)
                    , "class constraint" <:> MessageString (show predicate)
                    ]
        hints    = [ ("hint", MessageString "add the class constraint to the type signature") | original ]
    in TypeError [range] [oneliner] table hints

makeUnresolvedOverloadingError :: UHA_Source -> Constraint -> (PolyType, MonoType) -> TypeError
makeUnresolvedOverloadingError source (Constraint_Class description _ _) (functionType, usedAsType) =
    let message = [ MessageOneLiner (MessageString ("Don't know which instance to choose for " ++ description)) ]
        table   = [ "function" <:> MessageOneLineTree (oneLinerSource source)
                    , "type"     >:> MessageString (show functionType)
                    , "used as"  >:> MessageString (show usedAsType)
                    , "hint"     <:> MessageString ( "write an explicit type for this function" ++ 
                                "\n   e.g. (show :: [Int] -> String)")
                    ]
    in TypeError [rangeOfSource source] message table []

unfamilys :: Fresh m => [MonoType] -> m ([MonoType], [Constraint], [TyVar])
unfamilys ts = do   (args,cons,vars) <- unzip3 <$> mapM unfamily ts
                    return (args, concat cons, concat vars)

unfamily :: Fresh m => MonoType -> m (MonoType, [Constraint], [TyVar])
unfamily (MonoType_Fam f vs) = do   v <- fresh (string2Name "beta")
                                    return (var v, [Constraint_Unify (var v) (MonoType_Fam f vs) Nothing], [v])
unfamily (MonoType_App s t)  = do   (s',c1,v1) <- unfamily s
                                    (t',c2,v2) <- unfamily t
                                    return (MonoType_App s' t', c1 ++ c2, v1 ++ v2)
unfamily t                   = return (t, [], [])