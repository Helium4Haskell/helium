module Helium.CodeGeneration.Core.Strictness.Transform (transformModule, transformDeclaration) where

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Apply strict annotations on module
transformModule :: SolvedConstraints -> CoreModule -> CoreModule
transformModule env mod = mod{moduleDecls = map (transformDeclaration env) (moduleDecls mod)}  

-- Apply strict annotations on declarations, switch back original and annotated types
transformDeclaration :: SolvedConstraints -> CoreDecl -> CoreDecl
transformDeclaration env decl@DeclValue{} = decl{declType = t, valueValue = v}
  where
    t = transformType env $ declType decl
    v = transformExpression env $ valueValue decl
transformDeclaration env decl@DeclAbstract{}    = decl{declType = transformType env $ declType decl}
transformDeclaration env decl@DeclCon{}         = decl{declType = transformType env $ declType decl}
transformDeclaration env decl@DeclTypeSynonym{} = decl{declType = transformType env $ declType decl}
transformDeclaration _   decl                   = decl

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Type -> Type
transformType env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
  where
    t1' = transformType env t1
    t2' = transformType env t2
transformType env (TStrict t) = TStrict $ transformType env t
transformType env (TForall q k t) = TForall q k $ transformType env t
transformType env (TAnn (a1, r, a2) t) = TAnn (lookupVar a1 env, lookupVar r env, lookupVar a2 env) $ transformType env t
transformType _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> Expr -> Expr
-- Recursive has to stay recursive, bo transformation possible
transformExpression env (Let (Rec b) e) = Let (Rec (map (transformBind env) b)) $ transformExpression env e
-- Turn bind to strict if annotated with S
transformExpression env (Let (NonRec b@(Bind (Variable _ (TAnn (a, r, _) _)) _)) e) = Let binds $ transformExpression env e 
  where
    binds = if lookupVar a env == S && lookupVar r env == S then Strict bind else NonRec bind
    bind  = transformBind env b
-- Bind is already strict
transformExpression env (Let (Strict b) e) = Let (Strict (transformBind env b)) $ transformExpression env e
transformExpression env (Match i alts) = Match i $ map (transformAlt env) alts
transformExpression env (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (ApType e t) = ApType (transformExpression env e) (typeRemoveAnnotations t)
transformExpression env (Lam s (Variable x (TAnn (a, r, _) t)) e) = Lam (s || s') (Variable x t') e' 
  where
    -- Check if annotation variable is S
    s' = lookupVar a env == S && lookupVar r env == S
    e' = transformExpression env e
    t' = typeRemoveAnnotations t
transformExpression env (Forall q k e) = Forall q k $ transformExpression env e
transformExpression _ e = e -- Con, Lit and Var

-- Apply strict transformations on alts
transformAlt :: SolvedConstraints -> Alt -> Alt
transformAlt env (Alt p e) = Alt p' e'
  where
    p' = transformPat p
    e' = transformExpression env e

-- Apply strict transformations on pats
transformPat :: Pat -> Pat
transformPat (PatCon c t i) = PatCon c (map typeRemoveAnnotations t) i
transformPat p = p

-- Apply strict annotations on bind
transformBind :: SolvedConstraints -> Bind -> Bind
transformBind env (Bind (Variable x (TAnn _ t)) e) = Bind (Variable x t') e'
  where
    t' = typeRemoveAnnotations t
    e' = transformExpression env e

lookupVar :: SAnn -> SolvedConstraints -> SAnn
lookupVar (AnnVar x) env | elemMap x env = findMap x env
lookupVar ann _ = ann
