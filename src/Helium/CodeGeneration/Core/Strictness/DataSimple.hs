module Helium.CodeGeneration.Core.Strictness.DataSimple where

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Type

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment}

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable var env = env{typeEnv = typeEnv', relEnv = relEnv'}
  where
    typeEnv' = typeEnvAddVariable var $ typeEnv env
    relEnv'  = relEnvAddVariable  var $ relEnv env

envAddVariables :: [Variable] -> Environment -> Environment
envAddVariables vars env = foldr envAddVariable env vars

envAddBind :: Bind -> Environment -> Environment
envAddBind (Bind var _) = envAddVariable var

envAddBinds :: Binds -> Environment -> Environment
envAddBinds (Strict bind) env = envAddBind bind env
envAddBinds (NonRec bind) env = envAddBind bind env
envAddBinds (Rec binds) env = foldr envAddBind env binds

envAddPattern :: Pat -> Environment -> Environment
envAddPattern p env = envAddVariables x env
  where
    x = patternVariables (typeEnv env) p

relEnvAddVariable :: Variable -> RelevanceEnvironment -> RelevanceEnvironment
relEnvAddVariable (Variable x (TAp (TAnn a) _)) = insertMap x a

getVariablesType :: Bool -> Type -> IdSet
getVariablesType b (TAp (TAp (TCon TConFun) (TAp (TAnn a) t1)) t2) = unionSets [i1, i2, i3]
  where
    i1 = getVariablesType b t1
    i2 = getVariablesType b t2
    i3 = setFromList $ getVariablesAnn a
getVariablesType b (TAp t1 t2) = if b then unionSet (getVariablesType b t1) (getVariablesType b t2) else emptySet
getVariablesType b (TStrict t) = getVariablesType b t
getVariablesType b (TForall _ _ t) = getVariablesType b t
getVariablesType True (TAnn a) = setFromList $ getVariablesAnn a
getVariablesType _ _ = emptySet

getAnnotationsType :: Type -> IdSet
getAnnotationsType (TAp (TAp (TCon TConFun) (TAp (TAnn _) t1)) t2) = unionSet i1 i2
  where
    i1 = getAnnotationsType t1
    i2 = getAnnotationsType t2
getAnnotationsType (TAp t1 t2) = unionSet (getAnnotationsType t1) (getAnnotationsType t2)
getAnnotationsType (TStrict t) = getAnnotationsType t
getAnnotationsType (TForall _ _ t) = getAnnotationsType t
getAnnotationsType (TAnn a) = setFromList $ getVariablesAnn a
getAnnotationsType _ = emptySet

-- Add foralls for strictness annotations
forallify :: Bool -> Type -> Type
forallify b (TAp (TAnn a) t) = TAp (TAnn a) $ forallify b t
forallify b t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = listFromSet $ getVariablesType b t

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> Id -> AnnotationEnvironment
getAnnotations env rel var = case lookupMap var (relEnv env) of
      Just (AnnVar a) -> singleMap a rel
      _ -> emptyMap

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> AnnotationEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv env = f ++ g
  where
    f = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn $ relEnv env
    g = listFromSet $ unionSets $ map snd $ listFromMap $ mapMap getAnnotationsType $ typeEnvLocalValues $ typeEnv env

-- Containment
containment :: Environment -> SAnn -> AnnotationEnvironment
containment env con = mapFromList $ map (\x -> (x, con)) (getAnnotationVariablesEnv env)

strictBind :: Bind -> AnnotationEnvironment -> AnnotationEnvironment
strictBind (Bind (Variable _ (TAp (TAnn (AnnVar a)) _)) _) ae = ae'
    where
        ae' = insertMap a S ae

-- Turn bind to strict if annotated with S
bindToStrict :: SolvedConstraints -> Bind -> Bool
bindToStrict sc (Bind (Variable _ (TAp (TAnn a) _)) _) = lookupVar a sc == S

{-
    Annotate
-}

annotateType :: TypeEnvironment -> NameSupply -> Type -> Type
annotateType env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateType env supply t'
        where
            t' = typeNormalizeHead env t
annotateType env supply t@(TForall _ KAnn _) = annotateType env supply' t'
    -- Starts with strictness quantification, instantiate with fresh variable
    where
        (id, supply') = freshId supply
        (t', _) = annApplyList' t (AnnVar id) [] env
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    -- Function, place an annotation on the second argument (printed on the arrow)
    where
        (id, supply') = freshId supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = TAp (TAnn $ AnnVar id) $ annotateType env supply1 t1
        t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 (TAp (TAnn a) t2)) = TAp t1' (TAp (TAnn a) t2')
    -- Already annotated, no need to annotate again
    where
        (supply1, supply2) = splitNameSupply supply
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) = TAp t1' t2'
    -- Annotate applications to datatypes
    where
        (id, supply') = freshId supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = annotateType env supply1 t1
        t2' = TAp (TAnn $ AnnVar id) $ annotateType env supply2 t2      
annotateType env supply (TForall q k t) = TForall q k $ annotateType env supply t -- Non-strictness forall needs to stay
annotateType env supply (TStrict t) = annotateType env supply t -- Strictness information is moved to annotations
annotateType _ _ t = t

annotateTypeAbstract :: TypeEnvironment -> Type -> Type
annotateTypeAbstract env t
    -- Type is not in weak head normal form
    | t /= t' = annotateTypeAbstract env t'
        where
            t' = typeNormalizeHead env t
annotateTypeAbstract env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1a) t2'
    -- Function, place an annotation on the second argument (printed on the arrow)
    where
        t1' = annotateTypeAbstract env t1
        t1a = case t1' of
            (TStrict t) -> TAp (TAnn S) t
            _           -> TAp (TAnn L) t1'
        t2' = annotateTypeAbstract env t2
annotateTypeAbstract env (TAp t1 t2) = TAp t1' t2a
    -- Annotate applications to datatypes
    where
        t1' = annotateTypeAbstract env t1
        t2' = annotateTypeAbstract env t2      
        t2a = case t2' of
            (TStrict t) -> TAp (TAnn S) t
            _           -> TAp (TAnn L) t2'
annotateTypeAbstract env (TForall q k t) = TForall q k $ annotateTypeAbstract env t -- Non-strictness forall needs to stay
annotateTypeAbstract env (TStrict t) = TStrict $ annotateTypeAbstract env t -- Strictness information is moved to annotations
annotateTypeAbstract _ t = t

annotateBind :: Environment -> NameSupply -> Bind -> Bind
annotateBind env supply (Bind (Variable x t) e) = Bind (Variable x t') e
  where
    t' = annotateVarType env supply t

annotateVarType :: Environment -> NameSupply -> Type -> Type
annotateVarType env supply t = TAp (TAnn (AnnVar id)) t'
  where
    -- Fresh variable for relevance annotation
    (id, supply') = freshId supply
    -- Annotate inner type
    t' = annotateType (typeEnv env) supply' t
