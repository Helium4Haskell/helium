module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment
import Lvm.Core.Module
import Helium.CodeGeneration.Core.Strictness.Data

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
analyseDeclaration env decl@DeclValue{} = unionMap cv ct
  where
    cv = analyseExpression env S L (valueValue decl)
    ct = analyseType (typeNormalizeHead (typeEnv env) $ declType decl) t
    t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) True (valueValue decl)
analyseDeclaration _ _ = emptyMap

-- Run strictness analysis on expressions
analyseExpression :: Environment -> SAnn -> SAnn -> Expr -> Constraints
analyseExpression env rel app (Let b e) = unionMapWith meet c1 c2
  where
    c1   = analyseBinds env b
    env' = envAddBinds b env
    -- Containment, do not join with annotations on bind
    c2   = mapMapWithId (\x y -> if x `elem` bs then y else join app y) $ analyseExpression env' S app' e
    (bs, app') = getAnnotationVariablesBinds b
-- Only if an expression is strict on all alts it is strict
analyseExpression env rel app (Match _ alts) = unionMapsWith join $ map (analyseAlt env rel app) alts
analyseExpression env rel app (Ap e1 e2) = unionMapsWith meet [c1, c2, c3]
  where
    -- Analyse function
    c1 = analyseExpression env rel rel e1
    -- Get annotation from function
    t = typeOfCoreExpression (typeEnv env) True e1
    TAp (TAp (TCon TConFun) (TAnn (a1, r, a2) _)) _ = typeNormalizeHead (typeEnv env) t
    -- Analyse applicant under the join of the annotation and the rel
    c2 = analyseExpression env (join rel r) (join rel a1) e2
    -- Right applicativeness annotation should be equal to applicative context
    c3 = analyseAnnotation app a2
analyseExpression env rel app (ApType e _) = analyseExpression env rel app e
-- Expression in S relevance to see if the variable is strict, but contain with applicative
analyseExpression env _ app (Lam _ v@(Variable _ (TAnn (_, _, a2) _)) e) = mapMapWithId (\x y -> if inMap x then join app y else y) cs
  where
    cs = analyseExpression (envAddVariable v env) S a2 e
    (relAnn, appAnn) = getAnnotationVariablesEnv env
    inMap x = x `elemMap` relAnn || x `elemMap` appAnn
analyseExpression env rel app (Forall _ _ e) = analyseExpression env rel app e
analyseExpression env rel app (Var v) = unionMapWith meet (getConstraints env) cs
  where
    cs = getAnnotations env rel app v
analyseExpression env _ _ _ = getConstraints env -- Lit and Con

-- Run strictness analysis on alts
analyseAlt :: Environment -> SAnn -> SAnn -> Alt -> Constraints
analyseAlt env rel app (Alt pat e) = analyseExpression (envAddPattern pat env) rel app e

-- -- Run strictness analysis on binds
analyseBinds :: Environment -> Binds -> Constraints
analyseBinds env (NonRec b) = analyseBind env b
analyseBinds env (Strict b) = analyseBind env b
analyseBinds env b@(Rec bs) = unionMapsWith meet $ map (analyseBind env') bs
  where
    env' = envAddBinds b env

-- -- Run strictness analysis on bind
analyseBind :: Environment -> Bind -> Constraints
analyseBind env (Bind (Variable _ (TAnn (a, r, _) t)) e) = unionMap cs c1
  where
      -- Type of variable could be a function
    cs = analyseType t (typeOfCoreExpression (typeEnv env) True e)
    -- rel depends on the variable
    c1 = analyseExpression env r a e

-- Get constraints from function types
analyseType :: Type -> Type -> Constraints
-- Annotation variable in function type, set constraint equal to annotations on body
analyseType (TAp (TAp (TCon TConFun) (TAnn a1 t11)) t12)  (TAp (TAp (TCon TConFun) (TAnn a2 t21)) t22) = unionMaps [u1, u2, u3]
  where
    u1 = analyseType t11 t21
    u2 = analyseType t12 t22
    u3 = analyseAnnotations a1 a2
analyseType (TStrict t1) (TStrict t2) = analyseType t1 t2
analyseType (TForall _ _ t1) (TForall _ _ t2) = analyseType t1 t2
analyseType _ _ = emptyMap

analyseAnnotations :: Ann -> Ann -> Constraints
analyseAnnotations (a1, r, a2) (a1', r', a2') = unionMaps [ca1, cr, ca2]
  where
    ca1 = analyseAnnotation a1 a1'
    cr  = analyseAnnotation r r'
    ca2 = analyseAnnotation a2 a2'

analyseAnnotation :: SAnn -> SAnn -> Constraints
analyseAnnotation (AnnVar v) a            = singleMap v a
analyseAnnotation S          a@(Join _ _) = mapFromList $ zip (getAnnotationVariablesJoin a) (repeat S)
analyseAnnotation _          _            = emptyMap

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

-- Get all annotation variables in a binds
getAnnotationVariablesBinds :: Binds -> ([Id], SAnn)
getAnnotationVariablesBinds (NonRec b) = getAnnotationVariablesBind b
getAnnotationVariablesBinds (Strict b) = getAnnotationVariablesBind b
getAnnotationVariablesBinds (Rec bs)   = (concat vs, foldr join S anns)
  where
    (vs, anns) = unzip $ map getAnnotationVariablesBind bs

-- Get all annotation variables in a bind
getAnnotationVariablesBind :: Bind -> ([Id], SAnn)
getAnnotationVariablesBind (Bind (Variable _ (TAnn (a1, r, a2) _)) _) = (vs, a2)
  where
    vs = map fromAnn $ filter isAnn [a1, r]

-- Get all annotation variables in a join
getAnnotationVariablesJoin :: SAnn -> [Id]
getAnnotationVariablesJoin (AnnVar x) = [x]
getAnnotationVariablesJoin (Join x y) = getAnnotationVariablesJoin x ++ getAnnotationVariablesJoin y
getAnnotationVariablesJoin S          = []
getAnnotationVariablesJoin L          = []
getAnnotationVariablesJoin a          = error $ "Annotation " ++ show a ++ " occurs in type of function body"

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> (IdMap Id, IdMap Id)
getAnnotationVariablesEnv (Environment _ relEnv appEnv) = (f relEnv, f appEnv)
  where
    f env = mapMap fromAnn $ filterMap isAnn env

getConstraints :: Environment -> Constraints
getConstraints env = unionMap relcs appcs
  where
    (relAnn, appAnn) = getAnnotationVariablesEnv env
    (relcs , appcs ) = (getConstraints' relAnn, getConstraints' appAnn)
    getConstraints' vs = mapFromList $ map snd $ listFromMap $ mapMap (\x -> (x, L)) vs

getAnnotations :: Environment -> SAnn -> SAnn -> Id -> Constraints
getAnnotations (Environment _ relEnv appEnv) rel app var = unionMap (f relEnv rel) (f appEnv app)
  where
    f env con = case lookupMap var env of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap