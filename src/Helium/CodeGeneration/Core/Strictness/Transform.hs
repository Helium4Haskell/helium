module Helium.CodeGeneration.Core.Strictness.Transform (transformModule) where

import Helium.CodeGeneration.Core.Strictness.Analyse
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
transformDeclaration env (DeclAbstract n a m ar t ta c) = DeclAbstract n a m ar ta t c
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
deannotateType env t = t

-- Apply strict annotations on types
transformType :: Constraints -> Type -> Type
transformType env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
  where
    t1' = transformType env t1
    t2' = transformType env t2
transformType env (TStrict t) = TStrict $ transformType env t
transformType env (TForall q k t) = TForall q k $ transformType env t
transformType env (TAnn (AnnVar a) t) = TAnn s $ transformType env t
  where
    s = findMap a env
transformType env (TAnn a t) = TAnn a $ transformType env t
transformType env t = t

-- Apply strict annotations on expressions
transformExpression :: Constraints -> Expr -> Expr
transformExpression env (Let (Rec b) e) = Let (Rec (map (transformBind env) b)) $ transformExpression env e
transformExpression env (Let (NonRec (Bind (Variable x (TAnn (AnnVar a) t)) e1)) e2) = Let b e2' -- No transformation possible
  where
    r = if findMap a env == S then Strict else NonRec -- Turn bind to strict if annotated with S
    b = r (Bind (Variable x t') e1')
    t' = deannotateType env t
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (Let (Strict (Bind (Variable x (TAnn (AnnVar _) t)) e1)) e2) = Let b e2'
  where
    b = Strict (Bind (Variable x t') e1') -- Bind is already strict so annotation is irrelevant
    t' = deannotateType env t
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (Match i alts) = Match i $ map (transformAlt env) alts
transformExpression env (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (ApType e t) = ApType (transformExpression env e) (deannotateType env t)
transformExpression env (Lam s (Variable x (TAnn (AnnVar a) t)) e) = Lam s' (Variable x t') e' 
  where
    s' = s || (findMap a env == S) -- Lambda might already be strict
    e' = transformExpression env e
    t' = deannotateType env t
transformExpression env (Forall q k e) = Forall q k $ transformExpression env e
transformExpression _ expr = expr -- Con and Lit

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