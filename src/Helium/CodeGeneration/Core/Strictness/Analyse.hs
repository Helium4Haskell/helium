module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule, Constraints, join, meet) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment
import Lvm.Core.Module

type Constraints = IdMap SAnn

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = unionMaps $ map (analyseDeclaration env) (moduleDecls mod)
    where env  = typeEnvForModule mod

-- Run strictness analysis on declaration
analyseDeclaration :: TypeEnvironment -> CoreDecl -> Constraints
analyseDeclaration env decl@DeclValue{} = analyseExpression env S $ valueValue decl
analyseDeclaration _ _ = emptyMap

-- Run strictness analysis on expressions
analyseExpression :: TypeEnvironment -> SAnn -> Expr -> Constraints
-- Convert let to lambda for the purpose of this analysis
analyseExpression tyenv context (Let (NonRec (Bind v e1)) e2) = analyseExpression tyenv context (Ap (Lam False v e2) e1)
analyseExpression tyenv context (Let (Strict (Bind v e1)) e2) = analyseExpression tyenv context (Ap (Lam True  v e2) e1)
-- Recursive bindings cannot be inferred
analyseExpression tyenv context (Let bs e) = analyseExpression (typeEnvAddBinds bs tyenv) context e
-- Only if an expression is strict on all alts it is strict
analyseExpression tyenv context (Match _ alts) = foldr (unionMapWith join . analyseAlt tyenv context) emptyMap alts
analyseExpression tyenv context (Ap e1 e2) = unionMapWith meet c1 c2
  where
    -- Analyse function
    c1 = analyseExpression tyenv context e1
    -- Get annotation from function
    TAp (TAp (TCon TConFun) (TAnn a _)) _ = typeOfCoreExpression tyenv e1
    -- Analyse applicant under the join of the annotation and the context
    c2 = analyseExpression tyenv (join context a) e2
analyseExpression tyenv context (ApType e _) = analyseExpression tyenv context e
analyseExpression tyenv context (Lam _ v e) = analyseExpression (typeEnvAddVariable v tyenv) context e
analyseExpression tyenv context (Forall _ _ e) = analyseExpression tyenv context e
analyseExpression tyenv context e@(Var v) = mapFromList $ map snd $ listFromMap $ mapMapWithId (\x y -> (getVar y, isVar x v)) env
  where
    env = typeEnvLocalValues tyenv
    -- All local variables in the local environment should become lazy, the variable itself in context
    isVar v1 v2 = if v1 == v2 then context else L
analyseExpression tyenv _ _ = mapFromList $ map snd $ listFromMap $ mapMap (\x -> (getVar x, L)) env --Lit and Con
  where
    -- All local variables are lazy
    env = typeEnvLocalValues tyenv

-- Run strictness analysis on alts
analyseAlt :: TypeEnvironment -> SAnn -> Alt -> Constraints
analyseAlt tyenv context (Alt _ e) = analyseExpression tyenv context e

-- Get annotation variable from annotated type
getVar :: Type -> Id
getVar (TAnn (AnnVar x) _) = x
getVar _                   = error "All local variables should be annotated"

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