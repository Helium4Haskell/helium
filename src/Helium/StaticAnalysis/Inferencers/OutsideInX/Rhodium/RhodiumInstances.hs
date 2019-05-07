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
import qualified Unbound.LocallyNameless as UB
import qualified Unbound.LocallyNameless.Fresh as UB
import qualified Unbound.LocallyNameless.Alpha as UB
import qualified Unbound.LocallyNameless.Types as UB
import qualified Unbound.LocallyNameless.Subst as UB

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumErrors
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumGenerics

import Debug.Trace


instance Show (RType ConstraintInfo) where
    show (PType pt) = show pt
    show (MType mt) = show mt

          

instance FreshVariable FreshM TyVar where
    freshVariable = error "try not using fresh" -- fresh (string2Name "a")

instance (Fresh m, Monad m) => FreshVariable m TyVar where
    -- freshVariable :: m a
    freshVariable = error "try not using fresh" -- fresh (string2Name "a")

instance (CompareTypes m (RType ConstraintInfo), IsTouchable m TyVar, HasAxioms m (Axiom ConstraintInfo), IsTouchable m TyVar, Fresh m, Monad m) => CanCanon m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) where 
    -- canon :: Bool -> constraint -> m (Maybe ([touchable], [(touchable, types)], constraint))
    canon isGiven c = do 
        axs <- getAxioms
        canon' axs c 
            where
                canon' :: [Axiom ConstraintInfo] -> Constraint ConstraintInfo -> m (RuleResult ([TyVar], [(TyVar, RType ConstraintInfo)], [Constraint ConstraintInfo]))
                canon' axs (Constraint_Unify m1 m2 _) = do
                  ig <- greaterType (MType m1) (MType m2 :: RType ConstraintInfo)
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
                            | otherwise -> return NotApplicable
                canon' axs (Constraint_Inst m (PolyType_Mono cs pm) _) = return $ Applied ([], [], Constraint_Unify m pm Nothing : cs)                                  
                canon' axs (Constraint_Inst m p ci) = do 
                    (vs, c,t) <- instantiate p True
                    return $ Applied (vs, [], Constraint_Unify m t ci : c)
                canon' axs (Constraint_Class _ _ _) = return NotApplicable
                canon' axs c = error $ "Unknown canon constraint: " ++ show c


instantiate :: Fresh m => PolyType ConstraintInfo -> Bool -> m ([TyVar], [Constraint ConstraintInfo], MonoType)
instantiate (PolyType_Bind s b) tch = do
    (v,i) <- unbind b
    (vs, c,t) <- traceShowId <$> instantiate i tch
    
    let t' = fixVariableMapping s v t
    if tch then 
            return (v : vs, c, t')
    else 
            return ([], c, t')
instantiate (PolyType_Mono cs m) _tch = return ([], cs,m)

fixVariableMapping :: String -> TyVar -> MonoType -> MonoType
fixVariableMapping s v (MonoType_Var ms v') | v == v' = MonoType_Var (Just s) v'
                                        | otherwise = MonoType_Var ms v'
fixVariableMapping s v m@(MonoType_Con _) = m
fixVariableMapping s v m@(MonoType_App f a) = MonoType_App (fixVariableMapping s v f) (fixVariableMapping s v a)
fixVariableMapping s v m@(MonoType_Fam f ms) = MonoType_Fam f (map (fixVariableMapping s v) ms)



instance (HasGraph m touchable types constraint ci, CompareTypes m (RType ConstraintInfo), IsTouchable m TyVar, Fresh m, Monad m) => CanInteract m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
    --interact :: Bool -> constraint -> constraint -> m (RuleResult [constraint])
    interact isGiven c1 c2
        | c1 == c2 = return $ Applied [c1]
    interact isGiven c1@(Constraint_Unify (MonoType_Var _ v1) m1 _) c2@(Constraint_Unify t2@(MonoType_Fam f vs2) m2 _)
        | isFamilyFree m1, all isFamilyFree vs2, v1 `elem` (fv t2 :: [TyVar]) || v1 `elem` (fv m2 :: [TyVar]), isFamilyFree m2 =
                return $ Applied [c1, Constraint_Unify (subst v1 m1 t2) (subst v1 m1 m2) Nothing]
    interact isGiven c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | v1 == v2, isFamilyFree m1, isFamilyFree m2 = do
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify m1 m2 Nothing]
        | v1 `elem` (fv m2 :: [TyVar]), isFamilyFree m1, isFamilyFree m2 = do 
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify (var v2) (subst v1 m1 m2) Nothing]
    interact isGiven c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Class n ms2 _)
        | v1 `elem` (fv ms2 :: [TyVar]), all isFamilyFree ms2 = do 
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Class n (substs [(v1, m1)] ms2) Nothing]
    interact isGiven c1@(Constraint_Class _ _ _) c2@(Constraint_Class _ _ _) 
        | c1 == c2 = return $ Applied [c1]
    interact isGiven c1 c2 = return NotApplicable

instance (CompareTypes m (RType ConstraintInfo), HasAxioms m (Axiom ConstraintInfo), Fresh m) => CanSimplify m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | mv1 == m1 || mv2 == m2 = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Unify m1 mv1@(MonoType_Var _ v1) _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2) m2 _) 
        | mv1 == m1 || mv2 == m2 = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Class _ _ _) c2@(Constraint_Class _ _ _) 
        | c1 == c2 = return $ Applied []
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1) m1 _) c2@(Constraint_Class _ ms _) 
        | mv1 == m1 = return NotApplicable
        | v1 `elem` (fv ms :: [TyVar]), isFamilyFree m1, all isFamilyFree ms = do
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else
                return $ Applied [subst v1 m1 c2]
    simplify c1 c2 = return NotApplicable

loopAxioms :: Monad m => (Axiom ConstraintInfo -> m (RuleResult a)) -> [Axiom ConstraintInfo] -> m (RuleResult a)
loopAxioms f [] = return NotApplicable
loopAxioms f (x:xs) = do
    res <- f x
    if res == NotApplicable then
        loopAxioms f xs
    else 
        return res

isInjective :: [Axiom ConstraintInfo] -> String -> Bool
isInjective axioms s = any isInjective' axioms
    where 
        isInjective' (Axiom_Injective n) = n == s
        isInjective' _ = False

instance (HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, HasAxioms m (Axiom ConstraintInfo), Fresh m) => CanTopLevelReact m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) where
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

convertSubstitution :: [(TyVar, RType ConstraintInfo)] -> [(TyVar, MonoType)]
convertSubstitution = map (\(t, MType m) -> (t, m))

instance (IsTouchable m TyVar, Monad m, UniqueEdge m, UniqueVertex m, UniqueGroup m, Fresh m, HasGraph m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => CanConvertType m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
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
                

instance (IsTouchable m TyVar, HasGraph m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo, Fresh m, Monad m, UniqueVertex m, UniqueGroup m, UniqueEdge m) => CanConvertConstraint m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
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
        traceShowM (vars, given, wanted)
        return $ markTouchables (map (\v -> (v, priority + 2)) vars) (insertGraphs emptyTGGraph (given' ++ wanted'))
        --error $ show (vars, given, wanted)

instance IsEquality (RType ConstraintInfo) (Constraint ConstraintInfo) TyVar where
    -- isEquality :: constraint -> Bool
    isEquality (Constraint_Unify _ _ _) = True
    isEquality _    = False
    -- splitEquality :: constraint -> (types, types)
    splitEquality (Constraint_Unify m1 m2 _) = (MType m1, MType m2)
    allowInSubstitution (Constraint_Unify m1 m2 _) = isFamilyFree m1 && isFamilyFree m2
    allowInSubstitution _ = False


instance CanCompareTouchable TyVar (RType ConstraintInfo) where
    compareTouchable tyvar (MType v) = var tyvar == v
    compareTouchable tyvar (PType v) = var tyvar == v
    convertTouchable v = MType (var v) 
    applySubstitution sub (MType m) = MType $ substs (map (\(v, MType m) -> (v, m)) sub) m 
    applySubstitution sub (PType p) = PType $ substs (map (\(v, MType m) -> (v, m)) sub) p
    extractTouchable (MType (MonoType_Var _ v)) = Just v
    extractTouchable _ = Nothing

instance ConstraintSymbol (Constraint ConstraintInfo) where
    showConstraintSymbol (Constraint_Unify _ _ _) = "~"
    showConstraintSymbol (Constraint_Class s _ _) = "$" ++ s
    showConstraintSymbol (Constraint_Inst _ _ _) = ">"

instance ConvertConstructor (RType ConstraintInfo) where
    convertConstructor s = MType (MonoType_Con s)

instance (Fresh m, IsTouchable m TyVar) => CompareTypes m (RType ConstraintInfo) where
    greaterType (MType (MonoType_Var _ v1)) (MType (MonoType_Var  _ v2)) = greaterTouchable v1 v2
    greaterType m1 m2 = return $ m1 > m2
    mgu ms = MType <$> mostGeneralUnifier (map (\(MType m) -> m) ms)

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
                                | otherwise -> fresh (integer2Name 0) >>= (\v -> return ((mt, var v) : mapping, var v))
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
        mgu (mapping, mt) mv@(MonoType_Var _ v) = case lookup mv mapping of
            Nothing | mt == mv -> return ((mv, mv) : mapping, mv)
                    | otherwise -> fresh (integer2Name 0) >>= (\v' -> return ((mv, var v') : mapping, var v'))
        mgu mapping v = error $ show (mapping, v)
        convSub :: (MonoType, MonoType) -> Maybe (TyVar, MonoType)
        convSub (MonoType_Var _ v, m) = Just (v, m)
        convSub _ = Nothing

getTLVariableFromMonoType :: MonoType -> [TyVar]
getTLVariableFromMonoType (MonoType_Var _ v) = [v]
getTLVariableFromMonoType _ = []

instance FreeVariables (Constraint ConstraintInfo) TyVar where
    getFreeVariables = fv
    getFreeTopLevelVariables (Constraint_Unify m1 m2 _) = getTLVariableFromMonoType m1 ++ getTLVariableFromMonoType m2
    getFreeTopLevelVariables (Constraint_Inst m1 _ _) = getTLVariableFromMonoType m1
    getFreeTopLevelVariables (Constraint_Class _ _ _) = []
    getFreeTopLevelVariables c = error (show c)

instance FreeVariables (RType ConstraintInfo) TyVar where
    getFreeVariables (MType m) = fv m
    getFreeVariables (PType p) = fv p
    getFreeTopLevelVariables (MType m) = getTLVariableFromMonoType m

instance HasConstraintInfo (Constraint ConstraintInfo) ConstraintInfo where
    getConstraintInfo (Constraint_Unify _ _ ci) = ci
    getConstraintInfo (Constraint_Inst _ _ ci) = ci
    getConstraintInfo (Constraint_Exists _ ci) = ci
    getConstraintInfo (Constraint_Class _ _ ci) = ci
    getConstraintInfo c = error ("No constraint info for " ++ show c)
    setConstraintInfo ci (Constraint_Unify m1 m2 _) = Constraint_Unify m1 m2 (Just ci)


unfamilys :: Fresh m => [MonoType] -> m ([MonoType], [Constraint ConstraintInfo], [TyVar])
unfamilys ts = do   (args,cons,vars) <- unzip3 <$> mapM unfamily ts
                    return (args, concat cons, concat vars)

unfamily :: Fresh m => MonoType -> m (MonoType, [Constraint ConstraintInfo], [TyVar])
unfamily (MonoType_Fam f vs) = do   v <- fresh (string2Name "beta")
                                    return (var v, [Constraint_Unify (var v) (MonoType_Fam f vs) Nothing], [v])
unfamily (MonoType_App s t)  = do   (s',c1,v1) <- unfamily s
                                    (t',c2,v2) <- unfamily t
                                    return (MonoType_App s' t', c1 ++ c2, v1 ++ v2)
unfamily t                   = return (t, [], [])


functionSpineP :: Fresh m => PolyType ConstraintInfo -> m ([MonoType], MonoType)
functionSpineP (PolyType_Bind _ b) = unbind b >>= functionSpineP . snd
functionSpineP (PolyType_Mono _ m) = return (functionSpine m)

arityOfPolyType :: Fresh m => (PolyType ConstraintInfo) -> m Int
arityOfPolyType x = length . fst <$> functionSpineP x


instance Show Property where
    show FolkloreConstraint = "FolkloreConstraint"
    show (ConstraintPhaseNumber _) = "ConstraintPhaseNumber"
    show (HasTrustFactor f) = "HasTrustFactor: " ++ show f
    show (FuntionBindingEdge fb) = "FuntionBindingEdge" ++ show fb
    show (InstantiatedTypeScheme _) = "InstantiatedTypeScheme"
    show (SkolemizedTypeScheme _) = "SkolemizedTypeScheme"
    show (IsUserConstraint _ _) = "IsUserConstraint"
    show (WithHint (s, _) ) = "WithHint: " ++ s
    show (ReductionErrorInfo _) = "ReductionErrorInfo"
    show (FromBindingGroup) = "FromBindingGroup"
    show (IsImported _) = "IsImported"
    show (ApplicationEdge _ lc) = "ApplicationEdge" ++ show (map assignedType lc)
    show ExplicitTypedBinding = "ExplicitTypedBinding"
    show (ExplicitTypedDefinition _ _) = "ExplicitTypedDefinition"
    show (Unifier _ _) = "Unifier"
    show (EscapedSkolems _) = "EscapedSkolems"
    show (PredicateArisingFrom _) = "PredicateArisingFrom"
    show (TypeSignatureLocation _) = "TypeSignatureLocation"
    show (TypePair (t1, t2)) = "TypePair (" ++ show t1 ++ ", " ++ show t2 ++ ")" 
    show (MissingConcreteInstance n ms) = "MissingConcreteInstance(" ++ show n ++ " " ++ show ms ++ ")" 
    show (AddConstraintToTypeSignature ms cc) = "AddConstraintToTypeSignature " ++ show cc ++ " => " ++ show ms
    show (RelevantFunctionBinding fb) = "RelevantFunctionBinding: " ++ show fb
    show (ClassUsages cis) = "ClassUsages " ++ show cis
    show (AmbigiousClass c) = "AmbigiousClass " ++ show c
    show (FromGADT) = "FromGADT"
    show (UnreachablePattern m1 m2) = "UnreachablePattern(" ++ show m1 ++ ", " ++ show m2 ++ ")"
    show GADTPatternApplication = "GADTPatternApplication"
    show (PatternMatch v i mc) = "PatternMatch(" ++ show v ++ ", " ++ show i ++ "," ++ show mc ++ ")"
    show (PossibleTypeSignature ps) = "PossibleTypeSignature " ++ show ps
    show (GADTTypeSignature) = "GADTTypeSignature"
    show (MissingGADTTypeSignature mpt f bs) = "MissingGADTTypeSignature " ++ show mpt ++ ", " ++ show bs
    show (EscapingExistentital mt c) = "EscapingExistentital " ++ show mt ++ ", " ++ show c

    
instance Show ConstraintInfo where
    show x = location x ++ show (properties x) -- ++ fromMaybe [] (sortAndShowMessages . (:[]) <$> errorMessage x)

    