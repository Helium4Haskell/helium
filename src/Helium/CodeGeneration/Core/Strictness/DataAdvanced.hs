module Helium.CodeGeneration.Core.Strictness.DataAdvanced where

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Type

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment}

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable var env = env{typeEnv = typeEnv', relEnv = relEnv', appEnv = appEnv'}
  where
    typeEnv' = typeEnvAddVariable var $ typeEnv env
    relEnv'  = relEnvAddVariable  var $ relEnv env
    appEnv'  = appEnvAddVariable  var $ appEnv env

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
relEnvAddVariable (Variable x (TAp (TAnn _) (TAp (TAnn r) (TAp (TAnn _) _)))) = insertMap x r

appEnvAddVariable :: Variable -> ApplicativenessEnvironment -> ApplicativenessEnvironment
appEnvAddVariable (Variable x (TAp (TAnn a) (TAp (TAnn _) (TAp (TAnn _) _)))) = insertMap x a

getVariablesType :: Type -> IdSet
getVariablesType (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) = unionSets [i1, i2, i3]
  where
    i1 = getVariablesType t1
    i2 = getVariablesType t2
    i3 = setFromList (concatMap getVariablesAnn [a1, r, a2])
getVariablesType (TAp t1 t2) = unionSet (getVariablesType t1) (getVariablesType t2)
getVariablesType (TStrict t) = getVariablesType t
getVariablesType (TForall _ _ t) = getVariablesType t
getVariablesType _ = emptySet

getAnnotationsType :: Type -> IdSet
getAnnotationsType (TAp (TAp (TCon TConFun) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) t1)))) t2) = unionSet i1 i2
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
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> AnnotationEnvironment
getAnnotations env rel app var = unionMapWith join (f (relEnv env) rel) (f (appEnv env) app)
  where
    f env' con = case lookupMap var env' of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> AnnotationEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv env = f (relEnv env) ++ f (appEnv env) ++ g
  where
    f env' = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env'
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
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1a) t2'
    -- Function, place three annotations on the second argument (printed on the arrow)
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = annotateType env supply1 t1
        t1a = case t1 of
          TStrict _ -> TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id3) $ TAp (TAnn $ AnnVar id3) t1'
          _         -> TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id2) $ TAp (TAnn $ AnnVar id3) t1'
        t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) = TAp t1' t2'
    -- Annotate applications to datatypes
    where
        (supply1, supply2) = splitNameSupply supply
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2 
annotateType env supply (TForall q k t) = TForall q k $ annotateType env supply t -- Non-strictness forall needs to stay
annotateType env supply (TStrict t) = TStrict $ annotateType env supply t
annotateType _ _ t = t

annotateTypeAbstract :: TypeEnvironment -> NameSupply -> Type -> Type
annotateTypeAbstract env supply t = t' 
  where
    (t', _, _) = annotateTypeAbstract' env supply t

annotateTypeAbstract' :: TypeEnvironment -> NameSupply -> Type -> (Type, SAnn, SAnn)
annotateTypeAbstract' env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateTypeAbstract' env supply t'
        where
            t' = typeNormalizeHead env t
annotateTypeAbstract' env supply (TAp (TAp (TCon TConFun) t1) t2) = (TAp (TAp (TCon TConFun) t1a) t2', a', r')
    -- Function, place an annotation on the second argument (printed on the arrow)
    where
        (i, supply') = freshId supply
        ann = AnnVar i
        (supply1, supply2) = splitNameSupply supply'
        (t1', _, _) = annotateTypeAbstract' env supply1 t1
        (t2', a, r) = annotateTypeAbstract' env supply2 t2
        a' = join ann a
        r' = if arityFromType t2' == 0 then S else join ann r
        t1a = case t1' of
            (TStrict t) -> TAp (TAnn a') (TAp (TAnn r') (TAp (TAnn ann) t  ))
            _           -> TAp (TAnn L)  (TAp (TAnn L ) (TAp (TAnn ann) t1'))
annotateTypeAbstract' env supply (TAp t1 t2) = (TAp t1' t2', S, S)
    -- Annotate applications to datatypes
    where
        (supply1, supply2) = splitNameSupply supply
        (t1', _, _) = annotateTypeAbstract' env supply1 t1
        (t2', _, _) = annotateTypeAbstract' env supply2 t2
annotateTypeAbstract' env supply (TForall q k t) = (TForall q k t', a, r)
    where
        (t', a, r) = annotateTypeAbstract' env supply t -- Non-strictness forall needs to stay
annotateTypeAbstract' env supply (TStrict t) = (TStrict t', a, r)
    where
        (t', a, r) = annotateTypeAbstract' env supply t -- Strictness information is moved to annotations
annotateTypeAbstract' _ _ t = (t, S, S)

annotateBind :: Environment -> NameSupply -> Bind -> Bind
annotateBind env supply (Bind (Variable x t) e) = Bind (Variable x t') e
  where
    -- Fresh variables for relevance and both applicativeness
    (id1, id2, id3, supply') = threeIds supply
    -- Annotate inner type
    t' = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) (annotateType (typeEnv env) supply' t)))

annotateVarType :: Environment -> NameSupply -> Type -> Type
annotateVarType env supply t = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t'))
  where
    -- Fresh variables for relevance and both applicativeness
    (id1, id2, id3, supply') = threeIds supply
    -- Annotate inner type
    t' = annotateType (typeEnv env) supply' t
