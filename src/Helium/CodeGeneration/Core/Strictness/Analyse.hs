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
type AnnontationEnvironment = IdMap Id

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 annEnv  :: AnnontationEnvironment}

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = unionMaps $ map (analyseDeclaration env) (moduleDecls mod)
    where env  = Environment (typeEnvForModule mod) emptyMap

-- Run strictness analysis on declaration
analyseDeclaration :: Environment -> CoreDecl -> Constraints
analyseDeclaration env (DeclValue n a m t v c) = unionMap cv ct
  where
    cv = analyseExpression env S v
    ct = analyseType t $ typeOfCoreExpression (typeEnv env) v
analyseDeclaration _ _ = emptyMap

-- Run strictness analysis on expressions
analyseExpression :: Environment -> SAnn -> Expr -> Constraints
-- Information in bind has the context of the annotation variable related to the declared variable
analyseExpression env context (Let (NonRec (Bind v@(Variable x (TAnn _ t)) e1)) e2) = unionMap cs $ unionMapWith meet c1 c2
  where
    cs = analyseType t (typeOfCoreExpression (typeEnv env) e1)
    c1 = analyseExpression env context e1
    c2 = analyseExpression (envAddVariable v env) context e2
analyseExpression env context (Let (Strict (Bind v@(Variable x (TAnn _ t)) e1)) e2) = unionMap cs $ unionMapWith meet c1 c2
  where
    cs = analyseType t (typeOfCoreExpression (typeEnv env) e1)
    c1 = analyseExpression env context e1
    c2 = analyseExpression (envAddVariable v env) context e2
-- Recursive bindings need variable in bind so information is less precise
analyseExpression env context (Let b@(Rec bs) e) = unionMapWith meet c1 c2
  where
    env' = envAddBinds b env
    c1 = analyseBinds env' context bs
    c2 = analyseExpression env' context e
-- Only if an expression is strict on all alts it is strict
analyseExpression env context (Match _ alts) = foldr (unionMapWith join . analyseAlt env context) emptyMap alts
analyseExpression env context (Ap e1 e2) = unionMapWith meet c1 c2
  where
    -- Analyse function
    c1 = analyseExpression env context e1
    -- Get annotation from function
    a = case typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1  of
      TAp (TAp (TCon TConFun) (TAnn a _)) _ -> a
      _ -> L -- Forall function for tuple, has no annotation so assume L
    -- Analyse applicant under the join of the annotation and the context
    c2 = analyseExpression env (join context a) e2
analyseExpression env context (ApType e _) = analyseExpression env context e
analyseExpression env context (Lam _ v e) = analyseExpression (envAddVariable v env) context e
analyseExpression env context (Forall _ _ e) = analyseExpression env context e
analyseExpression env context (Var v) = mapFromList $ map snd $ listFromMap $ mapMapWithId (\x y -> (y, isVar x v)) (annEnv env)
  where
    -- All local variables in the local environment should become lazy, the variable itself in context
    isVar v1 v2 = if v1 == v2 then context else L
analyseExpression env _ _ = mapFromList $ map snd $ listFromMap $ mapMap (\x -> (x, L)) (annEnv env) --Lit and Con

-- Run strictness analysis on alts
analyseAlt :: Environment -> SAnn -> Alt -> Constraints
analyseAlt env context (Alt pat e) = analyseExpression (envAddPattern pat env) context e

-- Run strictness analysis on recursive binds
analyseBinds :: Environment -> SAnn -> [Bind] -> Constraints
analyseBinds env context bs = foldr (unionMapWith join) emptyMap $ map (analyseBind env context) bs

-- Run strictness analysis on recursive bind
analyseBind :: Environment -> SAnn -> Bind -> Constraints
analyseBind env context (Bind _ e) = analyseExpression env context e

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
analyseType (TAp (TAp (TCon TConFun) (TAnn (AnnVar a1) t11)) t12)  (TAp (TAp (TCon TConFun) (TAnn a2 t21)) t22) = insertMap a1 a2 $ unionMap u1 u2
  where
    u1 = analyseType t11 t21
    u2 = analyseType t12 t22
analyseType (TStrict t1) (TStrict t2) = analyseType t1 t2
analyseType (TForall _ _ t1) (TForall _ _ t2) = analyseType t1 t2
analyseType t1 t2 = emptyMap

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
annEnvAddVariable (Variable x (TAnn (AnnVar a) _)) env = insertMap x a env
annEnvAddVariable (Variable x t) _ = error ("Annotation not found: " ++ show (pretty t))
