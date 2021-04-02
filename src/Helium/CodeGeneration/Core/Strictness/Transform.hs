module Helium.CodeGeneration.Core.Strictness.Transform (transformModule) where

import Helium.CodeGeneration.Core.Strictness.Data
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- Apply strict annotations on module
transformModule :: Constraints -> CoreModule -> CoreModule
transformModule cs mod = mod{moduleDecls = map (transformDeclaration cs) (moduleDecls mod)}  

-- Apply strict annotations on declarations, switch back original and annotated types
transformDeclaration :: Constraints -> CoreDecl -> CoreDecl
transformDeclaration env (DeclValue n a m t ta v c) = DeclValue n a m ta t' v' c
  where
    t' = transformType env t
    v' = transformExpression env v
transformDeclaration _ (DeclAbstract n a m ar t ta c) = DeclAbstract n a m ar ta t c
transformDeclaration env (DeclCon n a m t f c) = DeclCon n a m t' f c
  where
    t' = deannotateType env t
transformDeclaration env (DeclTypeSynonym n a m s t c) = DeclTypeSynonym n a m s t' c
  where
    t' = deannotateType env t
transformDeclaration _ decl = decl

-- Remove annotations on types
deannotateType :: Constraints -> Type -> Type
deannotateType env (TAp (TAp (TCon TConFun) (TAnn _ t1)) t2) = TAp (TAp (TCon TConFun) t1') t2'
  where
    t1' = deannotateType env t1
    t2' = deannotateType env t2
deannotateType env (TStrict t) = TStrict $ deannotateType env t
deannotateType env (TForall q k t) = TForall q k $ deannotateType env t
deannotateType _ t = t

-- Apply strict annotations on types
transformType :: Constraints -> Type -> Type
transformType env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
  where
    t1' = transformType env t1
    t2' = transformType env t2
transformType env (TStrict t) = TStrict $ transformType env t
transformType env (TForall q k t) = TForall q k $ transformType env t
transformType env (TAnn (a1, r, a2) t) = TAnn (a1', r', a2') $ transformType env t
  where
    (a1', r', a2') = (replaceType env a1, replaceType env r, replaceType env a2)
transformType _ t = t

-- Apply strict annotations on expressions
transformExpression :: Constraints -> Expr -> Expr
-- Recursive has to stay recursive, bo transformation possible
transformExpression env (Let (Rec b) e) = Let (Rec (map (transformBind env) b)) $ transformExpression env e
-- Turn bind to strict if annotated with S
transformExpression env (Let (NonRec b@(Bind (Variable _ (TAnn (_, AnnVar a, _) _)) _)) e) = Let binds $ transformExpression env e 
  where
    binds = if findMap a env == S then Strict bind else NonRec bind
    bind  = transformBind env b
-- Bind is already strict
transformExpression env (Let (Strict b) e) = Let (Strict (transformBind env b)) $ transformExpression env e
transformExpression env (Match i alts) = Match i $ map (transformAlt env) alts
transformExpression env (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (ApType e t) = ApType (transformExpression env e) (deannotateType env t)
transformExpression env (Lam True  (Variable x (TAnn _          t)) e) = Lam True (Variable x t') e'
  where
    -- Lambda is already strict so no variable to solve
    e' = transformExpression env e
    t' = deannotateType env t
transformExpression env (Lam False (Variable x (TAnn (_, AnnVar a, _) t)) e) = Lam s    (Variable x t') e' 
  where
    -- Check if annotation variable is S or L
    s  = findMap a env == S
    e' = transformExpression env e
    t' = deannotateType env t
transformExpression env (Forall q k e) = Forall q k $ transformExpression env e
transformExpression _ (Con c) = Con c
transformExpression _ (Lit l) = Lit l
transformExpression _ (Var v) = Var v

-- Apply strict transformations on alts
transformAlt :: Constraints -> Alt -> Alt
transformAlt env (Alt p e) = Alt p' e'
  where
    p' = transformPat env p
    e' = transformExpression env e

-- Apply strict transformations on pats
transformPat :: Constraints -> Pat -> Pat
transformPat env (PatCon c t i) = PatCon c t' i
  where
    t' = map (deannotateType env) t
transformPat _ p = p

-- Apply strict annotations on bind
transformBind :: Constraints -> Bind -> Bind
transformBind env (Bind (Variable x (TAnn _ t)) e) = Bind (Variable x t') e'
  where
    t' = deannotateType env t
    e' = transformExpression env e


replaceType :: Constraints -> SAnn -> SAnn
replaceType env (AnnVar a) = findMap a env
replaceType _   a          = a 