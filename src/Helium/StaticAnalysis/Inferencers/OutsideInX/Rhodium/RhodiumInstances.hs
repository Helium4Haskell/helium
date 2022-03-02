{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DoAndIfThenElse #-}
--{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances where

import Control.Monad.Trans.State
import Control.Monad
import Control.Monad.IO.Class(MonadIO)

import Data.List
import Data.Maybe

import qualified Data.Map.Strict as M

import Rhodium.Core
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.GraphInstances()
import Rhodium.TypeGraphs.Graph
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Solver.Rules
import Rhodium.TypeGraphs.TGState

import Rhodium.TypeGraphs.Touchables 

import Unbound.Generics.LocallyNameless hiding (to, from)
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.Name
import qualified Unbound.Generics.LocallyNameless as UB
import qualified Unbound.Generics.LocallyNameless.Fresh as UB
import qualified Unbound.Generics.LocallyNameless.Alpha as UB
--import qualified Unbound.Generics.LocallyNameless.Types as UB
import qualified Unbound.Generics.LocallyNameless.Subst as UB

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumErrors
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumGenerics
import Debug.Trace (trace)
import Helium.StaticAnalysis.Miscellaneous.Unify (preMatch, InjectiveEnv, UnifyResultM (SurelyApart, Unifiable), applySubst, matchTy, SubstitutionEnv, unifyTy, applyOverInjArgs)
import Helium.Utils.Utils (internalError)

integer2Name :: Integer -> Name a
integer2Name = makeName ""

instance {-# Overlaps #-} Show (RType ConstraintInfo) where
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
                canon' axs ogc@(Constraint_Unify m1 m2 _) = do
                  ig <- greaterType (MType m1) (MType m2 :: RType ConstraintInfo)
                  if ig then 
                        return $ Applied ([], [], [Constraint_Unify m2 m1 Nothing])
                  else
                    case (m1, m2) of 
                        --_ | m1 > m2 -> return $ Applied ([], [], [Constraint_Unify m2 m1])
                        (MonoType_Con "[]" _, MonoType_Con "[]" _) -> return (Applied ([], [], []))
                        --(MonoType_Con "[]", MonoType_App _ _) -> error (show m2)
                        (MonoType_Con n1 _, MonoType_Con n2 _)
                            | n1 == n2 -> return $ Applied ([], [], [])
                            | otherwise -> return (Error labelIncorrectConstructors)
                        (MonoType_Con _ _, MonoType_App{}) -> return (Error labelIncorrectConstructors)
                        (MonoType_App{}, MonoType_Con _ _) -> return (Error labelIncorrectConstructors)
                        (f1 :-->: a1, f2 :-->: a2) -> return $ Applied ([], [], [Constraint_Unify f1 f2 Nothing, Constraint_Unify a1 a2 Nothing])
                        (MonoType_App f1 a1 _, MonoType_App f2 a2 _) -> return $ Applied ([], [], [Constraint_Unify f1 f2 Nothing, Constraint_Unify a1 a2 Nothing])
                        (MonoType_Var _ v1 _, MonoType_Var _ v2 _) 
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
                        (MonoType_Var _ v (Just rs), _)
                            | v `elem` (fvToList m2 :: [TyVar]), isFamilyFree m2 -> return (Error labelInfiniteType)
                            | isFamilyFree m2 -> return NotApplicable
                            | otherwise -> case m2 of
                                MonoType_Con _ _   -> return NotApplicable
                                MonoType_App c a ars -> 
                                    do (a2, con1, vars1) <- unfamily a
                                       (c2, con2, vars2) <- unfamily c
                                                        
                                       return $ Applied (vars1 ++ vars2, [], Constraint_Unify (insertReductionStep (var v) rs) (MonoType_App c2 a2 ars) Nothing : con1 ++ con2)
                                _ -> {-do 
                                    gt <- MType m1 `greaterType` MType m2
                                    if gt then 
                                        return Applied ([], [], [Constraint_Unify m2 m1])
                                    else-}
                                        return NotApplicable
                        (MonoType_Con _ _, MonoType_Var{}) -> return $ Applied ([], [], [Constraint_Unify m2 m1 Nothing])
                        (mf1@(MonoType_Fam f1 ts1 _), mf2@(MonoType_Fam f2 ts2 _))
                            | f1 == f2, 
                              (Just injIdx) <- injectiveArgs axs f1, 
                              length ts1 == length ts2 
                                -> return $ Applied ([], [], map (\i -> Constraint_Unify (insertReductionStep (ts1 !! i) (ts1 !! i, mf1, removeCI ogc, CanonReduction)) (insertReductionStep (ts2 !! i) (ts1 !! i, mf2, removeCI ogc, CanonReduction)) Nothing) injIdx)
                            | f1 == f2, isInjective axs f1, length ts1 /= length ts2 -> return $ Error $ ErrorLabel $ "Different Number of arguments for " ++ show ts1 ++ " and " ++ show ts2
                            | f1 == f2, null ts1 && null ts2 -> return $ Applied ([], [], [])
                            | f1 == f2, length ts1 == length ts2 -> return NotApplicable
                            | otherwise -> return NotApplicable
                        (MonoType_Fam f ts ri, _)
                            | (not . all isFamilyFree) ts -> 
                                do
                                    (ts2, cons, vars) <- unfamilys ts
                                    return (Applied (if isGiven then [] else vars, [], Constraint_Unify (MonoType_Fam f ts2 ri) m2 Nothing : cons))
                        (_, _)
                            | m1 == m2, isFamilyFree m1, isFamilyFree m2 -> return $ Applied ([], [], [])
                            | otherwise -> return NotApplicable
                canon' _ (Constraint_Inst m (PolyType_Mono cs pm) _) = return $ Applied ([], [], Constraint_Unify m pm Nothing : cs)
                canon' _ (Constraint_Inst m p ci) = do 
                    (vs, cci ,t) <- instantiate p True
                    return $ Applied (vs, [], Constraint_Unify m t ci : cci)
                canon' _ Constraint_Class{} = return NotApplicable
                canon' _ cci = error $ "Unknown canon constraint: " ++ show cci


instantiate :: Fresh m => PolyType ConstraintInfo -> Bool -> m ([TyVar], [Constraint ConstraintInfo], MonoType)
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
fixVariableMapping s v (MonoType_Var ms v' rs) | v == v'   = MonoType_Var (Just s) v' rs
                                               | otherwise = MonoType_Var ms v' rs
fixVariableMapping _ _ m@(MonoType_Con _ _)   = m
fixVariableMapping s v (MonoType_App f a rs)  = MonoType_App (fixVariableMapping s v f) (fixVariableMapping s v a) rs
fixVariableMapping s v (MonoType_Fam f ms rs) = MonoType_Fam f (map (fixVariableMapping s v) ms) rs

instance (HasGraph m touchable types constraint ci, HasAxioms m (Axiom ConstraintInfo), CompareTypes m (RType ConstraintInfo), IsTouchable m TyVar, Fresh m, Monad m) => CanInteract m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
    --interact :: Bool -> constraint -> constraint -> m (RuleResult [constraint])
    interact _ c1 c2
        | c1 == c2 = return $ Applied [c1]
    interact _ c1@(Constraint_Unify (MonoType_Var _ v1 _) m1 _) c2@(Constraint_Unify t2@(MonoType_Fam f vs2 _) m2 _)
        | isFamilyFree m1, all isFamilyFree vs2, v1 `elem` (fvToList t2 :: [TyVar]) || v1 `elem` (fvToList m2 :: [TyVar]), isFamilyFree m2 =
                return $ Applied [c1, Constraint_Unify (subst v1 m1 t2) (subst v1 m1 m2) Nothing]
    interact _ c1@(Constraint_Unify mv1@(MonoType_Var _ v1 _) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2 rs) m2 _) 
        | v1 == v2, isFamilyFree m1, isFamilyFree m2 = do
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify m1 m2 Nothing]
        | v1 `elem` (fvToList m2 :: [TyVar]), isFamilyFree m1, isFamilyFree m2 = do 
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Unify (insertReductionStepMaybe (var v2) rs) (subst v1 m1 m2) Nothing]
    interact _ c1@(Constraint_Unify (MonoType_Var _ v1 _) s1 _) (Constraint_Inst t2 s2 _)
        | v1 `elem` (fvToList t2 :: [TyVar]) || v1 `elem` (fvToList s2 :: [TyVar]), isFamilyFree s1
            = return $ Applied [c1, Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2) Nothing]
    interact _ c1@(Constraint_Unify mv1@(MonoType_Var _ v1 _) m1 _) c2@(Constraint_Class n ms2 _)
        | v1 `elem` (fvToList ms2 :: [TyVar]), all isFamilyFree ms2 = do 
            ig <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if ig then 
                return NotApplicable
            else
                return $ Applied [c1, Constraint_Class n (substs [(v1, m1)] ms2) Nothing]
    interact _ c1@(Constraint_Unify fm1@(MonoType_Fam f1 vs1 _) m1 _) c2@(Constraint_Unify fm2@(MonoType_Fam f2 vs2 _) m2 _)
        | f1 == f2, vs1 == vs2, isFamilyFree m1, isFamilyFree m2
            = return $ Applied [c1, Constraint_Unify m1 m2 Nothing]
        | f1 == f2, m1 == m2 = do
            (axs :: [Axiom ConstraintInfo]) <- getAxioms
            if isInjective axs f1
                then return $ Applied [Constraint_Unify fm1 fm2 Nothing]
                else return NotApplicable 
    interact _ c1@Constraint_Class {} c2@Constraint_Class{}
        | c1 == c2 = return $ Applied [c1]
    interact _ _ _ = return NotApplicable

instance (CompareTypes m (RType ConstraintInfo), HasAxioms m (Axiom ConstraintInfo), Fresh m) => CanSimplify m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1 _) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2 _) m2 _) 
        | mv1 == m1 || mv2 == m2 || not (isFamilyFree m1) || not (isFamilyFree m2) = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Unify m1 mv1@(MonoType_Var _ v1 _) _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2 _) m2 _) 
        | mv1 == m1 || mv2 == m2 = return NotApplicable
        | v1 == v2 = do 
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else 
                return $ Applied [Constraint_Unify m1 m2 Nothing]
    simplify c1@(Constraint_Class _ _ _) c2@(Constraint_Class _ _ _) 
        | c1 == c2 = return $ Applied []
    simplify (Constraint_Unify (MonoType_Var _ v1 _) s1 _) (Constraint_Inst t2 s2 _)
        | v1 `elem` (fvToList t2 :: [TyVar]) || v1 `elem` (fvToList s2 :: [TyVar]), isFamilyFree s1
            = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2) Nothing]
    simplify (Constraint_Unify mv1@(MonoType_Var _ v1 _) m1 _) c2@(Constraint_Class _ ms _) 
        | mv1 == m1 = return NotApplicable
        | v1 `elem` (fvToList ms :: [TyVar]), isFamilyFree m1, all isFamilyFree ms = do
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else
                return $ Applied [subst v1 m1 c2]
    simplify c1@(Constraint_Unify mv1@(MonoType_Var _ v1 _) m1 _) c2@(Constraint_Unify mv2@(MonoType_Var _ v2 _) m2 _) 
        | mv1 == m1 = return NotApplicable
        | v1 `elem` (fvToList m2 :: [TyVar]), isFamilyFree m1, isFamilyFree m2 = do
            gt <- greaterType (MType mv1) (MType m1 :: RType ConstraintInfo)
            if gt then 
                return NotApplicable
            else
                return $ Applied [subst v1 m1 c2]
    simplify c1@(Constraint_Unify mv@(MonoType_Var _ v _) m1 _) c2@(Constraint_Unify mf@(MonoType_Fam _ vs _) m2 _)
        | isFamilyFree m1, isFamilyFree m2, all isFamilyFree vs, v `elem` (fvToList mf :: [TyVar]) || v `elem` (fvToList m2 :: [TyVar])
            = return $ Applied [Constraint_Unify (subst v m1 mf) (subst v m1 m2) Nothing]
    simplify (Constraint_Unify (MonoType_Fam f1 vs1 _) m1 _) (Constraint_Unify (MonoType_Fam f2 vs2 _) m2 _)
        | f1 == f2, vs1 == vs2, isFamilyFree m1, isFamilyFree m2
            = return $ Applied [Constraint_Unify m1 m2 Nothing]
    -- simplify (Constraint_Inst t1 p1 _) (Constraint_Unify t2 p2 _)
    --     | t1 == t2 = return $ Applied [Constraint_Inst p2 p1 Nothing]
    simplify _ _ = return NotApplicable

loopAxioms :: Monad m => (Axiom ConstraintInfo -> m (RuleResult a)) -> [Axiom ConstraintInfo] -> m (RuleResult a)
loopAxioms _ [] = return NotApplicable 
loopAxioms f (x:xs) = do
    res <- f x
    if res == NotApplicable then
        loopAxioms f xs
    else 
        return res

isInjective :: [Axiom ConstraintInfo] -> String -> Bool
isInjective axs s = any isInjective' axs
    where 
        isInjective' (Axiom_Injective n _) = n == s
        isInjective' _ = False

injectiveArgs :: [Axiom ConstraintInfo] -> String -> Maybe [Int]
injectiveArgs [] _ = Nothing
injectiveArgs (Axiom_Injective as idx:axs) s 
    = if as == s
        then Just idx
        else injectiveArgs axs s
injectiveArgs (_:axs) s = injectiveArgs axs s


instance (
            HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo,
            HasAxioms m (Axiom ConstraintInfo), 
            Fresh m
        ) 
        => CanTopLevelReact m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) where
    topLevelReact _ (Constraint_Class n cs _) = getAxioms >>= loopAxioms topLevelReact'
        where
            topLevelReact' :: Axiom ConstraintInfo  -> m (RuleResult ([TyVar], [Constraint ConstraintInfo]))
            topLevelReact' ax@(Axiom_Class b) = do
                (aes, (ctx, cls, args)) <- unbind b
                if cls == n then do
                    let bes = fvToList ax :: [TyVar]
                    let unify = unifyTypes [] [] (zipWith (\c a -> Constraint_Unify c a (Nothing :: Maybe ConstraintInfo)) cs args) (aes \\ bes)
                    res <- runTG unify
                    case res of
                      Just s -> return $ Applied ([], substs (convertSubstitution s) ctx)
                      _  -> return NotApplicable
                else
                    return NotApplicable
            topLevelReact' _ = return NotApplicable
    topLevelReact given c@(Constraint_Unify mf@(MonoType_Fam f ms _) t _) = getAxioms >>= loopAxioms topLevelReact'  
        where
            topLevelReact' :: Axiom ConstraintInfo  -> m (RuleResult ([TyVar], [Constraint ConstraintInfo]))
            topLevelReact' ax@(Axiom_Unify b _) | all isFamilyFree ms, isFamilyFree t =
                do
                    (aes, (lhs, rhs)) <- unbind b
                    case lhs of
                        MonoType_Fam lF lMs _ | f == lF -> do
                            let bes = fvToList ax :: [TyVar]
                            let ustate = unifyTypes [] [] (zipWith (\m l -> Constraint_Unify m l (Nothing :: Maybe ConstraintInfo)) ms lMs) (aes \\ bes)
                            res <- runTG ustate :: m (Maybe [(TyVar, RType ConstraintInfo)])
                            case res of
                                (Just s) -> do
                                    let substRhs = substs (convertSubstitution s) rhs
                                    let newRhs = insertReductionStep substRhs (substRhs, mf, removeCI c, LeftToRight)
                                    return $ Applied (if given then [] else fvToList t, [Constraint_Unify newRhs t Nothing])
                                -- Try injectivity top level improvement when normal reaction fails
                                _ -> improveTopLevelFun given c ax
                        _ -> return NotApplicable
            topLevelReact' (Axiom_ClosedGroup af axs) =
                    if f == af
                        then reactClosedTypeFam given c axs
                        else return NotApplicable
            topLevelReact' _ = return NotApplicable
    topLevelReact _ _ = return NotApplicable

-- Improves top level constraints when the type family is injective
improveTopLevelFun :: (Fresh m, HasAxioms m (Axiom ConstraintInfo), MonadFail m) 
                   => Bool -> Constraint ConstraintInfo -> Axiom ConstraintInfo -> m (RuleResult ([TyVar], [Constraint ConstraintInfo]))
improveTopLevelFun given c@(Constraint_Unify fam@(MonoType_Fam f ms _) t _) (Axiom_Unify b _) | all isFamilyFree ms, isFamilyFree t =
    do
        (_, (lhs, rhs)) <- unbind b
        axs <- getAxioms
        case lhs of
            -- Only act when type family is injective and the names match.
            MonoType_Fam lF _ _ | f == lF, isInjective axs lF -> do
                -- Builds the injective env needed for preMatch and matchTy 
                ienv <- axsToInjectiveEnv axs --(trace ("Constraint and Ax: " ++ show c ++ ", " ++ show ax) axs)
                let injIdx = ienv M.! f
                -- If rhs and t preMatch (M(ti, t0))...
                case preMatch ienv rhs t of
                    SurelyApart -> return NotApplicable
                    Unifiable psubst -> do
                        -- And F (subst(args)) is reducible by the original...
                        let substLhs = applySubst psubst lhs
                        case matchTy lhs substLhs of
                            SurelyApart -> return NotApplicable
                            -- Deviate from paper, follow Cobalt, only focus on injective arguments.
                            Unifiable _ -> do
                                let substLhs = applyOverInjArgs psubst injIdx lhs
                                let newLhs = insertReductionStep substLhs (substLhs, fam, removeCI c, TopLevelImprovement)
                                return $ Applied (if given then [] else fvToList fam, [Constraint_Unify (applyOverInjArgs psubst injIdx lhs) fam Nothing]) -- Here we deviate from the paper and follow Cobalt (just substitute arguments with what we obtained)
            _ -> return NotApplicable 
improveTopLevelFun given c (Axiom_ClosedGroup _ axs) = loopAxioms (improveTopLevelFun given c) axs
improveTopLevelFun _ _ _ = return NotApplicable

-- Builds the InjectiveEnv from axioms
axsToInjectiveEnv :: (Fresh m, MonadFail m) => [Axiom ConstraintInfo] -> m InjectiveEnv
axsToInjectiveEnv = foldM f M.empty
    where
        f m (Axiom_Injective n injArgs) = return $ M.insert n injArgs m
        f m (Axiom_Unify b _)           = do
            (_, (MonoType_Fam g _ _, _)) <- unbind b
            case M.lookup g m of
              Nothing -> return $ M.insert g [] m
              Just _ -> return m
        f m _                           = return m

-- Handles the reaction of a closed type family application.
-- All instances are checked from top to bottom:
-- - First we match (using unifyTypes with carefully chosen touchable variables)
-- - If match succeeds, we check whether for all preceeding instances, the instance is compatible or apart.
-- - If that succeeds, we return the applied new constraint
-- The only difference wrt open type families, is that we match in an order and perform the compatApartness check.
reactClosedTypeFam :: (
                        Fresh m,
                        HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo,
                        HasAxioms m (Axiom ConstraintInfo)
                      )
                   => Bool
                   -> Constraint ConstraintInfo 
                   -> [Axiom ConstraintInfo] 
                   -> m (RuleResult ([Name MonoType], [Constraint ConstraintInfo]))
reactClosedTypeFam given = reactClosedTypeFam' [] 
    where
        reactClosedTypeFam' seen c@(Constraint_Unify mf@(MonoType_Fam _ ms _) t _) (ax@(Axiom_Unify b (Just _)):axs) 
            | all isFamilyFree ms, isFamilyFree t =
            do
                (aes, (lhs, rhs)) <- unbind b
                case lhs of
                  MonoType_Fam _ mts _ -> do
                      let bes = fvToList ax
                      let ustate = unifyTypes [] [] (zipWith (\m l -> Constraint_Unify m l Nothing) ms mts) (aes \\ bes)
                      res <- runTG ustate
                      case res of
                        Nothing -> do
                            -- Try injectivity toplevel improvement when normal matching fails.
                            improveRes <- improveTopLevelFun given c ax
                            case improveRes of
                              NotApplicable -> reactClosedTypeFam' (seen ++ [ax]) c axs 
                              a@(Applied _) -> return a
                              Error _ -> internalError "RhodiumInstances.hs" "reactClosedTypeFam" "improveTopLevelFun returned an error, should not happen!"
                        Just s -> do
                            compatApartRes <- checkCompatApartness seen ax c
                            if compatApartRes
                                then do
                                    let substRhs = substs (convertSubstitution s) rhs
                                    let newRhs = insertReductionStep substRhs (substRhs, mf, removeCI c, LeftToRight)
                                    return $ Applied (if given then [] else fvToList t, [Constraint_Unify (substs (convertSubstitution s) rhs) t Nothing])
                                else reactClosedTypeFam' (seen ++ [ax]) c axs 
                  _ -> return NotApplicable
        reactClosedTypeFam' _ _ _ = return NotApplicable

-- Compat was precomputed and is part of the Axiom_Unify construct (A Just idx where idx are the indices of previous instances with which it is compatible.
-- These instances need not to be checked for apartness so are removed.
checkCompatApartness :: (
                            Fresh m,
                            HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo,
                            HasAxioms m (Axiom ConstraintInfo)
                        )
                     =>  [Axiom ConstraintInfo] -> Axiom ConstraintInfo -> Constraint ConstraintInfo -> m Bool
checkCompatApartness seen ax@(Axiom_Unify _ (Just idx)) c = do
    let nonCompat = removeAt idx seen
    apartRes <- mapM (apartnessCheck c) nonCompat
    return $ all (==True) apartRes --LOL
    where
        removeAt :: [Int] -> [a] -> [a]
        removeAt ns xs = [x | (n,x) <- zip [0..] xs, n `notElem` ns]

-- apart(fam, lhs) = not(unify(lhs, flattened(fam))).
apartnessCheck :: (
                    Fresh m,
                    HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo,
                    HasAxioms m (Axiom ConstraintInfo)
                  )
                => Constraint ConstraintInfo -> Axiom ConstraintInfo -> m Bool
apartnessCheck (Constraint_Unify (MonoType_Fam f ts _) _ _) (Axiom_Unify b _) = do
     (ft, _, _) <- unfamilys ts
     (_, (lhs, _)) <- unbind b
     let nft = MonoType_Fam f ft Nothing
     case unifyTy lhs nft of
       SurelyApart -> return True
       Unifiable _ -> return False
     

convertSubstitution :: [(TyVar, RType ConstraintInfo)] -> [(TyVar, MonoType)]
convertSubstitution = map (\(t, MType m) -> (t, m))

instance (IsTouchable m TyVar, Monad m, UniqueEdge m, UniqueVertex m, UniqueGroup m, Fresh m, HasGraph m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo) => CanConvertType m TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo where
    convertType isOriginal groups priority (MType m) = do 
            mv <- getVertexFromGraph (MType m)
            --g <- getGraph
            if isJust mv then
                return (emptyTGGraph, fromJust mv)
            else
               convertTypeM m
        where
            convertTypeM (MonoType_Con n _) = do
                v <- uniqueVertex
                return (singletonGraph v TGConstant{
                    constant = n
                }, v)
            convertTypeM (MonoType_Var s mv _) = do
                v <- uniqueVertex
                graph <- getGraph
                isTch <- isVertexTouchable mv
                return  (singletonGraph v TGVariable{
                    variable = mv,
                    representation = maybe [] (:[]) s,
                    isTouchable = isTch
                }, v)
            convertTypeM m@(MonoType_App f a _) = do
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
            convertTypeM m@(MonoType_Fam s ms _) = do
                v <- uniqueVertex 
                ms' <- mapM (convertType isOriginal groups priority . MType) ms
                let vg = singletonGraph v TGApplication{
                    typeRep = MType m
                }
                constId <- uniqueVertex
                let cg = (singletonGraph constId TGConstant{
                    constant = s
                }, constId)
                edgeIds <- replicateM (length ms + 1) uniqueEdge
                let typeEdges = zipWith3 (\eid (_, vc) i -> typeEdge eid i isOriginal v vc) 
                                    edgeIds (cg : ms') [0..]
                return (foldr (\((ng, _), te) og -> 
                    mergeGraphsWithEdges False [te] og ng
                    ) vg (zip (cg : ms') typeEdges), v)
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
        return $ markTouchables (map (\v -> (v, priority + 2)) vars) (insertGraphs emptyTGGraph (given' ++ wanted'))
        --error $ show (vars, given, wanted)

instance IsEquality (Axiom ConstraintInfo) (RType ConstraintInfo) (Constraint ConstraintInfo) TyVar where
    -- isEquality :: constraint -> Bool
    isEquality (Constraint_Unify _ _ _) = True
    isEquality _    = False
    -- splitEquality :: constraint -> (types, types)
    splitEquality (Constraint_Unify m1 m2 _) = (MType m1, MType m2)
    -- Interesting case for a constraint (G a ~ x) with G injective in argument a and x touchable. Could later be solved in a certain usage
    -- so we allow it in the substitution.
    -- This is subject to change.
    allowInSubstitution axs thcs (Constraint_Unify (MonoType_Fam f mts _) (MonoType_Var _ v _) _)
        -- G is injective
        | (Just injArgs) <- injectiveArgs axs f
        -- x is touchable
        , v `elem` (thcs :: [TyVar]) 
        = let
            -- all argument vars
            allVars = filter isVar mts
            -- all injective vars
            injVars = [x | (n, x@(MonoType_Var _ v1 _)) <- zip [0..] mts, n `elem` injArgs, v1 `notElem` thcs]
            isVar MonoType_Var{} = True
            isVar _                  = False
            -- allVars and injVars must be equal, this says: all remaining vars are injective and may be determined when we know x.
            in allVars == injVars
    allowInSubstitution _ _ (Constraint_Unify (MonoType_Fam f1 m1 _) (MonoType_Fam f2 m2 _) _) = f1 == f2 && m1 == m2
    allowInSubstitution _ _ (Constraint_Unify m1 m2 _) = isFamilyFree m1 && isFamilyFree m2
    allowInSubstitution _ _ _ = False


instance CanCompareTouchable TyVar (RType ConstraintInfo) where
    compareTouchable tyvar (MType v) = var tyvar == v
    compareTouchable tyvar (PType v) = var tyvar == v
    convertTouchable v = MType (var v) 
    applySubstitution sub (MType m) = MType $ substs (map (\(v, MType m) -> (v, m)) sub) m 
    applySubstitution sub (PType p) = PType $ substs (map (\(v, MType m) -> (v, m)) sub) p
    extractTouchable (MType (MonoType_Var _ v _)) = Just v
    extractTouchable _ = Nothing

instance ConstraintSymbol (Constraint ConstraintInfo) where
    showConstraintSymbol (Constraint_Unify _ _ _) = "~"
    showConstraintSymbol (Constraint_Class s _ _) = "$" ++ s
    showConstraintSymbol (Constraint_Inst _ _ _) = ">"

instance ConvertConstructor (RType ConstraintInfo) where
    convertConstructor s = MType (MonoType_Con s Nothing)

instance (Fresh m, IsTouchable m TyVar) => CompareTypes m (RType ConstraintInfo) where
    greaterType (MType (MonoType_Var _ v1 _)) (MType (MonoType_Var  _ v2 _)) = greaterTouchable v1 v2
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
        mgu (mapping, MonoType_Var _ v1 _) mt = case lookup (var v1) mapping  of
                Nothing -> return ((var v1, mt) : mapping, mt)
                Just mtv -> case lookup mt mapping of
                    Nothing     | mt == mtv -> return ((mt, mt) : mapping, mt)
                                | otherwise -> fresh (integer2Name 0) >>= (\v -> return ((mt, var v) : mapping, var v))
                    Just mtv'   | mtv == mtv' -> return (mapping, mtv)
                                | otherwise -> (\v -> ((mtv, var v) : (mtv', var v) : (var v, var v) : mapping, var v)) <$> fresh (integer2Name 0) 
        mgu (mapping, m1@(MonoType_Con s1 rs)) m2@(MonoType_Con s2 _) =
            case lookup m1 mapping of
                Nothing | s1 == s2 -> return (mapping, MonoType_Con s1 rs)
                        | otherwise -> (\v -> ((m1, var v) : (m2, var v) : (var v, var v) : mapping, var v)) <$> fresh (integer2Name 0) 
                Just mv -> return (mapping, mv)
        mgu (mapping, MonoType_App f1 a1 _) (MonoType_App f2 a2 _) = do
            (mapping', fr) <- mgu (mapping, f1) f2
            (mapping'', ar) <- mgu (mapping', a1) a2
            return (mapping'', MonoType_App fr ar Nothing)
        mgu (mapping, mt) mv@(MonoType_Var _ v _) = case lookup mv mapping of
            Nothing | mt == mv -> return ((mv, mv) : mapping, mv)
                    | otherwise -> fresh (integer2Name 0) >>= (\v' -> return ((mv, var v') : mapping, var v'))
        mgu mapping v = error $ show (mapping, v)
        convSub :: (MonoType, MonoType) -> Maybe (TyVar, MonoType)
        convSub (MonoType_Var _ v _, m) = Just (v, m)
        convSub _ = Nothing

getTLVariableFromMonoType :: MonoType -> [TyVar]
getTLVariableFromMonoType (MonoType_Var _ v _) = [v]
getTLVariableFromMonoType _ = []

instance FreeVariables (Constraint ConstraintInfo) TyVar where
    getFreeVariables = fvToList
    getFreeTopLevelVariables (Constraint_Unify m1 m2 _) = getTLVariableFromMonoType m1 ++ getTLVariableFromMonoType m2
    getFreeTopLevelVariables (Constraint_Inst m1 _ _) = getTLVariableFromMonoType m1
    getFreeTopLevelVariables (Constraint_Class _ _ _) = []
    getFreeTopLevelVariables c = error (show c)

instance FreeVariables (RType ConstraintInfo) TyVar where
    getFreeVariables (MType m) = fvToList m
    getFreeVariables (PType p) = fvToList p
    getFreeTopLevelVariables (MType m) = getTLVariableFromMonoType m


unfamilys :: Fresh m => [MonoType] -> m ([MonoType], [Constraint ConstraintInfo], [TyVar])
unfamilys ts = do   (args,cons,vars) <- unzip3 <$> mapM unfamily ts
                    return (args, concat cons, concat vars)

unfamily :: Fresh m => MonoType -> m (MonoType, [Constraint ConstraintInfo], [TyVar])
unfamily (MonoType_Fam f vs rs) = do   v <- fresh (string2Name "beta")
                                       return (var v, [Constraint_Unify (var v) (MonoType_Fam f vs rs) Nothing], [v])
unfamily (MonoType_App s t rs)  = do   (s',c1,v1) <- unfamily s
                                       (t',c2,v2) <- unfamily t
                                       return (MonoType_App s' t' rs, c1 ++ c2, v1 ++ v2)
unfamily t                   = return (t, [], [])


functionSpineP :: Fresh m => PolyType ConstraintInfo -> m ([MonoType], MonoType)
functionSpineP (PolyType_Bind _ b) = unbind b >>= functionSpineP . snd
functionSpineP (PolyType_Mono _ m) = return (functionSpine m)

arityOfPolyType :: Fresh m => (PolyType ConstraintInfo) -> m Int
arityOfPolyType x = length . fst <$> functionSpineP x

    