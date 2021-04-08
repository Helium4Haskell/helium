module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment
import Lvm.Core.Module
import Helium.CodeGeneration.Core.Strictness.Data
import Data.List

-- Annotation variables per local definition by let or lambda
type RelevanceEnvironment       = IdMap SAnn
type ApplicativenessEnvironment = IdMap SAnn

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment}

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = unionMaps $ map (analyseDeclaration env) (moduleDecls mod)
    where
      env  = Environment (typeEnvForModule mod) emptyMap emptyMap

-- Run strictness analysis on declaration
analyseDeclaration :: Environment -> CoreDecl -> Constraints
analyseDeclaration env decl@DeclValue{} = unionMap cs' ct
  where
    (cs, es, us) = analyseExpression env S L (valueValue decl)
    -- Apply substitutions
    cs' = foldMapWithId replace (foldMapWithId replace cs us) (foldMapWithId replace es us)
    ct = analyseType (typeNormalizeHead (typeEnv env) $ declType decl) t
    t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) True (valueValue decl)
analyseDeclaration _ _ = emptyMap

-- Run strictness analysis on expressions
-- Returns a triplet of constraints, applicative equalities and signature-body equalities
analyseExpression :: Environment -> SAnn -> SAnn -> Expr -> (Constraints, Constraints, Constraints)
analyseExpression env rel app (Let b e) = (cs, es, us)
  where
    cs = unionMapWith meet c1 (containment env rel c2)
    es = unionMapsWith meet [analyseAnnotation app' app, e1, e2]
    us = unionMap u1 u2
    -- Analyse bind
    (c1, e1, u1, app') = analyseBinds env rel b
    -- Analyse body      
    env' = envAddBinds b env
    (c2, e2, u2) = analyseExpression env' S app' e

-- Only if an expression is strict on all alts it is strict
analyseExpression env rel app (Match _ alts) = (unionMapsWith join cs, unionMapsWith join es, unionMaps us)
  where
    (cs, es, us) = unzip3 $ map (analyseAlt env rel app) alts
analyseExpression env rel app (Ap e1 e2) = (cs, eqs, us)
  where
    cs = unionMapWith meet c1 c2
    eqs = unionMapsWith meet [analyseAnnotation a2 app, eq1, eq2]
    us = unionMap u1 u2
    -- Analyse function
    (c1, eq1, u1) = analyseExpression env rel rel e1
    -- Get annotation from function
    t = typeOfCoreExpression (typeEnv env) True e1
    TAp (TAp (TCon TConFun) (TAnn (a1, r, a2) _)) _ = typeNormalizeHead (typeEnv env) t
    -- Analyse applicant under the join of the annotations and the relevance context
    (c2, eq2, u2) = analyseExpression env (join rel r) (join rel a1) e2
analyseExpression env rel app (ApType e _) = analyseExpression env rel app e
-- Expression in S relevance to see if the variable is strict, but contain with applicative
analyseExpression env _ app (Lam _ v@(Variable _ (TAnn (_, _, a2) _)) e) = (containment env app cs, es, us)
  where
    (cs, es, us) = analyseExpression (envAddVariable v env) S a2 e
analyseExpression env rel app (Forall _ _ e) = analyseExpression env rel app e
-- No equalities from vars, cons and lits
analyseExpression env rel app (Var v) = (unionMapWith meet (getLConstraints env) cs, emptyMap, emptyMap)
  where
    cs = getAnnotations env rel app v
analyseExpression env _ _ _ = (getLConstraints env, emptyMap, emptyMap) -- Lit and Con

-- Run strictness analysis on alts
-- Returns a triplet of constraints, applicative equalities and signature-body equalities
analyseAlt :: Environment -> SAnn -> SAnn -> Alt -> (Constraints, Constraints, Constraints)
analyseAlt env rel app (Alt pat e) = analyseExpression (envAddPattern pat env) rel app e

-- Run strictness analysis on binds
-- Returns a quadruplet of constraints, applicative equalities, signature-body equalities and the right applicative annotation
analyseBinds :: Environment -> SAnn -> Binds -> (Constraints, Constraints, Constraints, SAnn)
analyseBinds env rel (Strict b) = analyseBind env rel b
analyseBinds env rel (NonRec b) = analyseBind env rel b
analyseBinds env rel b@(Rec bs) = (unionMapsWith meet cs, unionMapsWith meet es, unionMaps us, foldr join S as)
  where
    (cs, es, us, as) = unzip4 $ map (analyseBind (envAddBinds b env) rel) bs

-- Run strictness analysis on bind
-- Returns a quadruplet of constraints, applicative equalities, signature-body equalities and the right applicative annotation
analyseBind :: Environment -> SAnn -> Bind -> (Constraints, Constraints, Constraints, SAnn)
analyseBind env rel (Bind (Variable _ (TAnn (a1, r, a2) t)) e) = (cs, es, unionMap r1 r2, a2)
  where
    -- Type of variable could be a function
    r2 = analyseType t (typeOfCoreExpression (typeEnv env) True e)
    -- rel depends on the variable
    (cs, es, r1) = analyseExpression env (join rel r) (join rel a1) e

-- Get constraints from function types
analyseType :: Type -> Type -> Constraints
-- Annotation variable in function type, set constraints equal to annotations on body
analyseType (TAp (TAp (TCon TConFun) (TAnn (a1, r, a2) t11)) t12)  (TAp (TAp (TCon TConFun) (TAnn (a1', r', a2') t21)) t22) = unionMaps [u1, u2, u3]
  where
    u1 = analyseType t11 t21
    u2 = analyseType t12 t22
    u3 = unionMaps [analyseAnnotation a1 a1', analyseAnnotation r r', analyseAnnotation a2 a2']
analyseType (TStrict t1) (TStrict t2) = analyseType t1 t2
analyseType (TForall _ _ t1) (TForall _ _ t2) = analyseType t1 t2
analyseType _ _ = emptyMap

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

-- Type signature has variable, set equal to annotation from body
analyseAnnotation :: SAnn -> SAnn -> Constraints
analyseAnnotation (AnnVar v) a            = singleMap v a
analyseAnnotation _          _            = emptyMap

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> ([Id], [Id])
getAnnotationVariablesEnv (Environment _ relEnv appEnv) = (f relEnv, f appEnv)
  where
    f env = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> Constraints
getLConstraints env = unionMap relcs appcs
  where
    (relAnn, appAnn) = getAnnotationVariablesEnv env
    (relcs , appcs ) = (getLConstraints' relAnn, getLConstraints' appAnn)
    getLConstraints' vs = mapFromList $ map (\x -> (x, L)) vs

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> Constraints
getAnnotations (Environment _ relEnv appEnv) rel app var = unionMap (f relEnv rel) (f appEnv app)
  where
    f env con = case lookupMap var env of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Containment
containment :: Environment -> SAnn -> Constraints -> Constraints
containment env con = mapMapWithId (\x y -> if x `elem` relAnn || x `elem` appAnn then join con y else y)
  where
    (relAnn, appAnn) = getAnnotationVariablesEnv env

-- Apply equalities 
replace :: Id -> SAnn -> Constraints -> Constraints
replace a ann cs = if elemMap a cs && isAnn ann then cs'' else cs'
  where
    -- Replace all value occurences
    cs' = mapMap replace' cs
    -- Replace all key occurences
    cs'' = insertMap (fromAnn ann) (findMap a cs') (deleteMap a cs')
    replace' :: SAnn -> SAnn
    replace' (AnnVar a') | a == a' = ann
    replace' (Join l r)  = join (replace' l) (replace' r)
    replace' (Meet l r)  = meet (replace' l) (replace' r)
    replace' s = s
  