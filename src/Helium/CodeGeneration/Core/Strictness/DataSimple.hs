module Helium.CodeGeneration.Core.Strictness.DataSimple where

import Data.List

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
                                 vars    :: IdSet}

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

envAddVars :: IdSet -> Environment -> Environment
envAddVars is env = env{vars = unionSet is (vars env)}

getVariablesType :: Bool -> Type -> [Id]
getVariablesType b (TAp (TAp (TCon TConFun) (TAp (TAnn a) t1)) t2) = nub $ concat [i1, i2, i3]
  where
    i1 = getVariablesType b t1
    i2 = getVariablesType b t2
    i3 = getVariablesAnn a
getVariablesType b (TAp t1 t2) = nub $ getVariablesType b t1 ++ getVariablesType b t2
getVariablesType b (TStrict t) = getVariablesType b t
getVariablesType b (TForall _ _ t) = getVariablesType b t
getVariablesType True (TAnn a) = getVariablesAnn a
getVariablesType _ _ = []

-- Add foralls for strictness annotations
forallify :: Bool -> Type -> Type
forallify b (TAp (TAnn a) t) = TAp (TAnn a) $ forallify b t
forallify b t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = getVariablesType b t

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
getAnnotationVariablesEnv env = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn $ relEnv env

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
