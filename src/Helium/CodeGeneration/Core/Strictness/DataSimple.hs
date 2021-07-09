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

getVariablesType :: Type -> IdSet
getVariablesType (TAp (TAp (TCon TConFun) (TAp (TAnn a) t1)) t2) = unionSets [i1, i2, i3]
  where
    i1 = getVariablesType t1
    i2 = getVariablesType t2
    i3 = setFromList $ getVariablesAnn a
getVariablesType (TAp t1 t2) = unionSet (getVariablesType t1) (getVariablesType t2)
getVariablesType (TStrict t) = getVariablesType t
getVariablesType (TForall _ _ t) = getVariablesType t
getVariablesType _ = emptySet

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
forallify :: Maybe IdSet -> Type -> Type
forallify is (TAp (TAnn a) t) = TAp (TAnn a) $ forallify is t
forallify is t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = listFromSet $ maybe (getVariablesType t) (intersectionSet (getVariablesType t)) is

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
containment :: Environment -> SAnn -> AnnotationEnvironment -> AnnotationEnvironment
containment env con ae = unionMapWith join ae $ mapFromList $ map (\x -> (x, con)) $ getAnnotationVariablesEnv env

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
        (i, supply') = freshId supply
        (t', _) = annApplyList' t (AnnVar i) [] env
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    -- Function, place an annotation on the second argument (printed on the arrow)
    where
        (i, supply') = freshId supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = case t1 of
          TStrict _ -> TAp (TAnn S) $ annotateType env supply1 t1
          _         -> TAp (TAnn $ AnnVar i) $ annotateType env supply1 t1
        t2' = annotateType env supply2 t2
-- annotateType env supply (TAp t1 (TAp (TAnn a) t2)) = TAp t1' (TAp (TAnn a) t2')
--     -- Already annotated, no need to annotate again
--     where
--         (supply1, supply2) = splitNameSupply supply
--         t1' = annotateType env supply1 t1
--         t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) 
  | isTup t1  = TAp t1' t2a
  | otherwise = TAp t1' t2'
    -- Annotate applications to datatypes
    where
        (i, supply') = freshId supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2
        t2a = case t2 of
          TStrict _ -> TAp (TAnn S) t2'
          _         -> TAp (TAnn $ AnnVar i) t2'
annotateType env supply (TForall q k t) = TForall q k $ annotateType env supply t -- Non-strictness forall needs to stay
annotateType env supply (TStrict t) = TStrict $ annotateType env supply t
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
annotateTypeAbstract env (TAp t1 t2)
  | isTup t1 = TAp t1' t2a
  | otherwise = TAp t1' t2'
    -- Annotate applications to datatypes
    where
        t1' = annotateTypeAbstract env t1
        t2' = annotateTypeAbstract env t2      
        t2a = case t2' of
            (TStrict t) -> TAp (TAnn S) t
            _           -> TAp (TAnn L) t2'
annotateTypeAbstract env (TForall q k t) = TForall q k $ annotateTypeAbstract env t -- Non-strictness forall needs to stay
annotateTypeAbstract env (TStrict t) = TStrict $ annotateTypeAbstract env t
annotateTypeAbstract _ t = t

annotateBind :: Environment -> NameSupply -> Bind -> Bind
annotateBind env supply (Bind (Variable x t) e) = Bind (Variable x t') e
  where
    -- Fresh variable for relevance annotation
    (i, _) = freshId supply
    -- Annotate inner type
    t' = TAp (TAnn (AnnVar i)) $ annotateTypeRec (typeEnv env) t

annotateVarType :: Environment -> NameSupply -> Type -> Type
annotateVarType env supply t = TAp (TAnn (AnnVar i)) t'
  where
    -- Fresh variable for relevance annotation
    (i, supply') = freshId supply
    -- Annotate inner type
    t' = annotateType (typeEnv env) supply' t

annotateTypeRec :: TypeEnvironment -> Type -> Type
annotateTypeRec env t
    | t /= t' = annotateTypeRec env t'
        where
            t' = typeNormalizeHead env t
annotateTypeRec env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) (TAp (TAnn S) t1')) t2'
    where
        t1' = annotateTypeRec env t1
        t2' = annotateTypeRec env t2
annotateTypeRec env (TAp t1 t2)
  | isTup t1  = TAp t1' (TAp (TAnn L) t2')
  | otherwise = TAp t1' t2'
    where
        t1' = annotateTypeRec env t1
        t2' = annotateTypeRec env t2
annotateTypeRec env (TStrict t) = TStrict $ annotateTypeRec env t
annotateTypeRec env (TForall q k t) = TForall q k $ annotateTypeRec env t
annotateTypeRec _ t = t
