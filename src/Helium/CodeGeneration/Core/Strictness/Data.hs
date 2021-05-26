module Helium.CodeGeneration.Core.Strictness.Data where

import Data.List
import qualified Data.Set as S

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment

-- Keys are annotation variables, values are the equality/join/meet
type AnnotationEnvironment = IdMap SAnn

-- Annotation variables per local definition by let or lambda
type RelevanceEnvironment       = IdMap SAnn
type ApplicativenessEnvironment = IdMap SAnn

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment}

-- Constraint set, l < r
type Constraints = S.Set Constraint
data Constraint = Constraint SAnn SAnn deriving (Eq, Ord, Show)
type SolvedConstraints = IdMap SAnn

isAnn :: SAnn -> Bool
isAnn (AnnVar _) = True
isAnn _          = False

fromAnn :: SAnn -> Id
fromAnn (AnnVar x) = x
fromAnn _          = error "fromAnn"

isCustomAnn :: Custom -> Bool
isCustomAnn (CustomDecl (DeclKindCustom n) _) = stringFromId n == "strictness"
isCustomAnn  _ = False

fromCustomAnn :: Custom -> Type
fromCustomAnn (CustomDecl (DeclKindCustom _) [CustomType t]) = t

annEnvToConstraints :: AnnotationEnvironment -> Constraints
annEnvToConstraints = S.fromList . map snd . listFromMap . mapMapWithId (\x y -> Constraint y (AnnVar x))

-- Get all variables in an annotation or type
getVariablesAnn :: SAnn -> [Id]
getVariablesAnn (AnnVar x) = [x]
getVariablesAnn (Join x y) = getVariablesAnn x ++ getVariablesAnn y
getVariablesAnn (Meet x y) = getVariablesAnn x ++ getVariablesAnn y
getVariablesAnn _          = []

typeRemoveStrictnessQuantification :: Type -> Type
typeRemoveStrictnessQuantification (TForall _ KAnn t) = typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TForall q k t) = TForall q k $ typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TStrict t) = TStrict $ typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TAp t1 t2) = TAp (typeRemoveStrictnessQuantification t1) (typeRemoveStrictnessQuantification t2)
typeRemoveStrictnessQuantification t = t

typeRemoveAnnotations :: Type -> Type
typeRemoveAnnotations (TAp (TAnn _) t1) = typeRemoveAnnotations t1
typeRemoveAnnotations (TAp t1 t2) = TAp (typeRemoveAnnotations t1) (typeRemoveAnnotations t2)
typeRemoveAnnotations (TForall _ KAnn t) = typeRemoveAnnotations t
typeRemoveAnnotations (TForall q k t) = TForall q k $ typeRemoveAnnotations t
typeRemoveAnnotations (TStrict t) = TStrict $ typeRemoveAnnotations t
typeRemoveAnnotations (TAnn a) = error $ "Annotation " ++ show a ++ " occurs outside application"
typeRemoveAnnotations t = t

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable var (Environment typeEnv relEnv appEnv) = Environment typeEnv' relEnv' appEnv'
  where
    typeEnv' = typeEnvAddVariable var typeEnv
    relEnv'  = relEnvAddVariable  var relEnv
    appEnv'  = appEnvAddVariable  var appEnv

envAddVariables :: [Variable] -> Environment -> Environment
envAddVariables vars env = foldr envAddVariable env vars

envAddBind :: Bind -> Environment -> Environment
envAddBind (Bind var _) = envAddVariable var

envAddBinds :: Binds -> Environment -> Environment
envAddBinds (Strict bind) env = envAddBind bind env
envAddBinds (NonRec bind) env = envAddBind bind env
envAddBinds (Rec binds) env = foldr envAddBind env binds

envAddPattern :: Pat -> Environment -> Environment
envAddPattern p (Environment typeEnv relEnv appEnv) = Environment (typeEnvAddPattern p typeEnv) relEnv appEnv

relEnvAddVariable :: Variable -> RelevanceEnvironment -> RelevanceEnvironment
relEnvAddVariable (Variable x (TAp _ (TAp (TAnn r) _))) = insertMap x r

appEnvAddVariable :: Variable -> ApplicativenessEnvironment -> ApplicativenessEnvironment
appEnvAddVariable (Variable x (TAp (TAnn a) _)) = insertMap x a

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv (Environment _ relEnv appEnv) = f relEnv ++ f appEnv
  where
    f env = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env

-- Add foralls for strictness annotations
forallify :: Type -> Type
forallify (TAp (TAnn a) t) = TAp (TAnn a) $ forallify t
forallify t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = getVariablesType t

getVariablesType :: Type -> [Id]
getVariablesType (TAp t1 t2) = nub $ getVariablesType t1 ++ getVariablesType t2
getVariablesType (TStrict t) = getVariablesType t
getVariablesType (TForall _ _ t) = getVariablesType t
getVariablesType (TAnn a) = getVariablesAnn a
getVariablesType _ = []
