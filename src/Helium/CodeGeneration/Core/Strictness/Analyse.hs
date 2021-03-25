module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule, Constraints, join, meet) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment
import Lvm.Core.Module
import Text.PrettyPrint.Leijen (pretty)

-- Constraint set, keys are annotation variables, values are the equality/join/meet
type Constraints = IdMap SAnn

-- Annotation variables per local definition by let or lambda
type AnnontationEnvironment = IdMap SAnn

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 annEnv  :: AnnontationEnvironment}

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = unionMaps $ map (analyseDeclaration env) (moduleDecls mod)
    where env  = Environment (typeEnvForModule mod) emptyMap

-- Run strictness analysis on declaration
analyseDeclaration :: Environment -> CoreDecl -> Constraints
analyseDeclaration env decl@DeclValue{} = unionMap cv ct
  where
    cv = analyseExpression env S (valueValue decl)
    ct = analyseType (declType decl) $ typeOfCoreExpression (typeEnv env) (valueValue decl)
analyseDeclaration _ _ = emptyMap

-- Run strictness analysis on expressions
analyseExpression :: Environment -> SAnn -> Expr -> Constraints
analyseExpression env context (Let b e) = unionMapWith meet c1 c2
  where
    c1   = analyseBinds env b
    env' = envAddBinds b env
    -- Containment, do not join with annotations on bind
    c2   = mapMapWithId (\x y -> if x `elem` bs then y else join context y) $ analyseExpression env' S e
    bs   = getAnnotationVariablesBinds b
-- Only if an expression is strict on all alts it is strict
analyseExpression env context (Match _ alts) = foldr (unionMapWith join . analyseAlt env context) emptyMap alts
analyseExpression env context (Ap e1 e2) = unionMapWith meet c1 c2
  where
    -- Analyse function
    c1 = analyseExpression env context e1
    -- Get annotation from function
    a = case typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1  of
      TAp (TAp (TCon TConFun) (TAnn a' _)) _ -> a'
      _ -> L -- Forall function for tuple, has no annotation so assume L
    -- Analyse applicant under the join of the annotation and the context
    c2 = analyseExpression env (join context a) e2
analyseExpression env context (ApType e _) = analyseExpression env context e
-- Strict lambda, so no constraint on annotation variable, hence evaluation can be done under context
analyseExpression env context (Lam True v e) = analyseExpression (envAddVariable v env) context e
-- Expression in S context to see if the variable is strict, but join with context to contain all other variables
analyseExpression env context (Lam False v@(Variable _ (TAnn a _)) e) = mapMap (\x -> if x /= a then join context x else x) cs
  where
    cs = analyseExpression (envAddVariable v env) S e
analyseExpression env context (Forall _ _ e) = analyseExpression env context e
analyseExpression env context (Var v) = mapFromList $ map snd $ listFromMap $ mapMapWithId (\x y -> (y, isVar x v)) vs
  where
    -- All local variables in the local environment should become lazy, the variable itself in context
    vs = getAnnotationVariablesEnv env
    isVar v1 v2 = if v1 == v2 then context else L
analyseExpression env _ (Lit _) = mapFromList $ map snd $ listFromMap $ mapMap (\x -> (x, L)) vs
  where
    vs = getAnnotationVariablesEnv env
analyseExpression env _ (Con _) = mapFromList $ map snd $ listFromMap $ mapMap (\x -> (x, L)) vs
  where
    vs = getAnnotationVariablesEnv env
analyseExpression _ _ e = error $ "analyseExpression: " ++ show (pretty e) ++ " not supported"

-- Run strictness analysis on alts
analyseAlt :: Environment -> SAnn -> Alt -> Constraints
analyseAlt env context (Alt pat e) = analyseExpression (envAddPattern pat env) context e

-- -- Run strictness analysis on binds
analyseBinds :: Environment -> Binds -> Constraints
analyseBinds env (NonRec b) = analyseBind env b
analyseBinds env (Strict b) = analyseBind env b
analyseBinds env b@(Rec bs) = foldr (unionMapWith meet . analyseBind env') emptyMap bs
  where
    env' = envAddBinds b env

-- -- Run strictness analysis on bind
analyseBind :: Environment -> Bind -> Constraints
analyseBind env (Bind (Variable _ (TAnn a t)) e) = unionMap cs c1
  where
      -- Type of variable could be a function
    cs = analyseType t (typeOfCoreExpression (typeEnv env) e)
    -- Context depends on the variable
    c1 = analyseExpression env a e

-- Join and meet
join, meet :: SAnn -> SAnn -> SAnn
join L _ = L
join _ L = L
join S x = x
join x S = x
join x y = Join x y

meet S _ = S
meet _ S = S
meet L x = x
meet x L = x
meet x y = Meet x y

-- Get constraints from function types
analyseType :: Type -> Type -> Constraints
-- Annotation variable in function type, set constraint equal to annotations on body
analyseType (TAp (TAp (TCon TConFun) (TAnn (AnnVar a1) t11)) t12)  (TAp (TAp (TCon TConFun) (TAnn a2 t21)) t22) = insertMap a1 a2 $ unionMap u1 u2
  where
    u1 = analyseType t11 t21
    u2 = analyseType t12 t22
-- Annotation in function type is strict, set constraint for all annotation variables in body to strict
analyseType (TAp (TAp (TCon TConFun) (TAnn S t11)) t12)  (TAp (TAp (TCon TConFun) (TAnn a2 t21)) t22) = unionMaps [u1, u2, u3]
  where
    u1 = analyseType t11 t21
    u2 = analyseType t12 t22
    u3 = mapFromList $ zip (getAnnotationVariablesJoin a2) (repeat S)
analyseType (TStrict t1) (TStrict t2) = analyseType t1 t2
analyseType (TForall _ _ t1) (TForall _ _ t2) = analyseType t1 t2
analyseType _ _ = emptyMap

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable v (Environment typeEnv annEnv) = Environment typeEnv' annEnv'
  where
    typeEnv' = typeEnvAddVariable v typeEnv
    annEnv'  = annEnvAddVariable v annEnv

envAddVariables :: [Variable] -> Environment -> Environment
envAddVariables vars env = foldr envAddVariable env vars

envAddBind :: Bind -> Environment -> Environment
envAddBind (Bind var _) = envAddVariable var

envAddBinds :: Binds -> Environment -> Environment
envAddBinds (Strict bind) env = envAddBind bind env
envAddBinds (NonRec bind) env = envAddBind bind env
envAddBinds (Rec binds) env = foldr envAddBind env binds

envAddPattern :: Pat -> Environment -> Environment
envAddPattern p (Environment typeEnv annEnv) = Environment (typeEnvAddPattern p typeEnv) annEnv

annEnvAddVariable :: Variable -> AnnontationEnvironment -> AnnontationEnvironment
annEnvAddVariable (Variable x (TAnn a _)) env = insertMap x a env

-- Get all annotation variables in a binds
getAnnotationVariablesBinds :: Binds -> [Id]
getAnnotationVariablesBinds (NonRec b) = getAnnotationVariablesBind b
getAnnotationVariablesBinds (Strict b) = getAnnotationVariablesBind b
getAnnotationVariablesBinds (Rec bs)   = concatMap getAnnotationVariablesBind bs

-- Get all annotation variables in a bind
getAnnotationVariablesBind :: Bind -> [Id]
getAnnotationVariablesBind (Bind (Variable _ (TAnn (AnnVar a) _)) _) = [a]
getAnnotationVariablesBind _                                         = []

-- Get all annotation variables in a join
getAnnotationVariablesJoin :: SAnn -> [Id]
getAnnotationVariablesJoin (AnnVar x) = [x]
getAnnotationVariablesJoin (Join x y) = getAnnotationVariablesJoin x ++ getAnnotationVariablesJoin y
getAnnotationVariablesJoin S          = []
getAnnotationVariablesJoin a          = error $ "Annotation " ++ show a ++ " occurs in type of function body"

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> IdMap Id
getAnnotationVariablesEnv (Environment _ env) = mapMap fromAnn $ filterMap isAnn env
  where
    isAnn :: SAnn -> Bool
    isAnn (AnnVar _) = True
    isAnn _          = False
    fromAnn :: SAnn -> Id
    fromAnn (AnnVar x) = x