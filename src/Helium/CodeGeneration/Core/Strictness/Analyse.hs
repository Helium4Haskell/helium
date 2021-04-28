module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule, analyseDeclaration) where

import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Annotation variables per local definition by let or lambda
type RelevanceEnvironment       = IdMap SAnn
type ApplicativenessEnvironment = IdMap SAnn

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment}

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = S.unions $ map (analyseDeclaration $ typeEnvForModule mod) (moduleDecls mod)

-- Run strictness analysis on declaration
analyseDeclaration :: TypeEnvironment -> CoreDecl -> Constraints
analyseDeclaration env decl@DeclValue{} = S.unions [c1, c2, c3]
  where
    -- Annotation environment and constraints from body
    (ae, c1) = analyseExpression env' S app (valueValue decl)
    -- Turn annotation environment into constraints
    c2 = annEnvToConstraints ae
    -- Constraints on type-body relations
    c3 = analyseType env (declType decl) (typeOfCoreExpression env True $ valueValue decl)
    -- If function is fully saturated we can analyse in S context, otherwise L
    app = case arityFromType $ typeNormalizeHead env (declType decl) of
      0 -> S
      _ -> L
    env' = Environment env emptyMap emptyMap
analyseDeclaration _ _ = S.empty

-- Run strictness analysis on expressions
analyseExpression :: Environment -> SAnn -> SAnn -> Expr -> (AnnotationEnvironment, Constraints)
analyseExpression env rel app (Let b e) = (ae, cs)
  where
    ae = unionMapWith meet a1 a2'
    cs = S.insert (app `Constraint` app') $ S.union c1 c2
    -- Analyse bind
    (a1, c1, app') = analyseBinds env rel b
    -- Analyse body      
    (a2, c2) = analyseExpression (envAddBinds b env) S app' e
    a2' = unionMapWith join a2 $ containment env rel
-- Only if an expression is strict on all alts it is strict
analyseExpression env rel app (Match _ alts) = (unionMapsWith join ae, S.unions cs)
  where
    (ae, cs) = unzip $ map (analyseAlt env rel app) alts
analyseExpression env rel app (Ap e1 e2) = (ae, cs)
  where
    ae = unionMapWith meet ae1 ae2
    cs = S.insert (app `Constraint` a2) $ S.union c1 c2
    -- Analyse function
    (ae1, c1) = analyseExpression env rel rel e1
    -- Get annotation from function
    t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) True e1
    TAp (TAp (TCon TConFun) (TAnn (a1, r, a2) _)) _ = t
    -- Analyse applicant under the join of the annotations and the relevance context
    (ae2, c2) = analyseExpression env (join rel r) (join rel a1) e2
analyseExpression env rel app (ApType e _) = analyseExpression env rel app e
-- Expression in S relevance to see if the variable is strict, but contain with applicative
analyseExpression env _ app (Lam _ v@(Variable _ (TAnn (_, _, a2) _)) e) = (ae', cs)
  where
    (ae, cs) = analyseExpression (envAddVariable v env) S a2 e
    ae' = unionMapWith join ae $ containment env app
analyseExpression env rel app (Forall _ _ e) = analyseExpression env rel app e
-- No equalities from vars, cons and lits
analyseExpression env rel app (Var v) = (unionMapWith meet (getLConstraints env) ae, S.empty)
  where
    ae = getAnnotations env rel app v
analyseExpression env _ _ _ = (getLConstraints env, S.empty) -- Lit and Con

-- Run strictness analysis on alts
-- Returns a tuple of constraints and applicative equalities
analyseAlt :: Environment -> SAnn -> SAnn -> Alt -> (AnnotationEnvironment, Constraints)
analyseAlt env rel app (Alt pat e) = analyseExpression (envAddPattern pat env) rel app e

-- Run strictness analysis on binds
-- Returns a triplet of constraints, applicative equalities, and the right applicative annotation
analyseBinds :: Environment -> SAnn -> Binds -> (AnnotationEnvironment, Constraints, SAnn)
analyseBinds env rel (Strict b) = analyseBind env rel b
analyseBinds env rel (NonRec b) = analyseBind env rel b
analyseBinds env rel b@(Rec bs) = (unionMapsWith meet ae, S.unions cs, foldr join S ap)
  where
    (ae, cs, ap) = unzip3 $ map (analyseBind (envAddBinds b env) rel) bs

-- Run strictness analysis on bind
-- Returns a triplet of constraints, applicative equalities, and the right applicative annotation
analyseBind :: Environment -> SAnn -> Bind -> (AnnotationEnvironment, Constraints, SAnn)
analyseBind env rel (Bind (Variable _ (TAnn (a1, r, a2) t)) e) = (ae, S.union c1 c2, a2)
  where
    (ae, c1) = analyseExpression env (join rel r) (join rel a1) e
    c2 = analyseType (typeEnv env) t (typeOfCoreExpression (typeEnv env) True e)

-- Analyse type
analyseType :: TypeEnvironment -> Type -> Type -> Constraints
analyseType env (TAp (TAp (TCon TConFun) t11) t12)  (TAp (TAp (TCon TConFun) t21) t22) = S.union c1 c2
  where
    c1 = analyseType env t11 t21
    c2 = analyseType env t12 t22
analyseType env (TStrict t1) (TStrict t2) = analyseType env t1 t2
analyseType env (TForall _ _ t1) (TForall _ _ t2) = analyseType env t1 t2
analyseType env (TAnn (a1, r, a2) t1) (TAnn (a1', r', a2') t2) = S.union c1 c2
  where
    c1 = S.fromList [a1' `Constraint` a1, r' `Constraint` r, a2' `Constraint` a2]
    c2 = analyseType env t1 t2
analyseType env t1 t2 | t1 == t2  = S.empty
                      | otherwise = analyseType env (typeNormalizeHead env t1) (typeNormalizeHead env t2)

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable v (Environment typeEnv relEnv appEnv) = Environment typeEnv' relEnv' appEnv'
  where
    typeEnv' = typeEnvAddVariable v typeEnv
    relEnv'  = relEnvAddVariable  v relEnv
    appEnv'  = appEnvAddVariable  v appEnv

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
relEnvAddVariable (Variable x (TAnn (_, r, _) _)) = insertMap x r

appEnvAddVariable :: Variable -> ApplicativenessEnvironment -> ApplicativenessEnvironment
appEnvAddVariable (Variable x (TAnn (a, _, _) _)) = insertMap x a

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv (Environment _ relEnv appEnv) = f relEnv ++ f appEnv
  where
    f env = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> ApplicativenessEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> ApplicativenessEnvironment
getAnnotations (Environment _ relEnv appEnv) rel app var = unionMap (f relEnv rel) (f appEnv app)
  where
    f env con = case lookupMap var env of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Containment
containment :: Environment -> SAnn -> AnnotationEnvironment
containment env con = mapFromList $ map (\x -> (x, con)) (getAnnotationVariablesEnv env)
