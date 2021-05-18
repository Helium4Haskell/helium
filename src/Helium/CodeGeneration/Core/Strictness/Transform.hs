module Helium.CodeGeneration.Core.Strictness.Transform (transformModule, transformDeclaration) where

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.Instantiate (forallify)
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Apply strict annotations on module
transformModule :: SolvedConstraints -> Bool -> CoreModule -> CoreModule
transformModule env poly mod = mod{moduleDecls = map (transformDeclaration tyenv env poly) (moduleDecls mod)}
  where
    tyenv = typeEnvForModule mod

-- Apply strict annotations on declarations
transformDeclaration :: TypeEnvironment -> SolvedConstraints -> Bool -> CoreDecl -> CoreDecl
transformDeclaration tyenv env poly decl@DeclValue{} = decl{declType = t', valueValue = v}
  where
    -- Foralliy if the analysis is polyvariant
    t' = if poly then forallify tyenv t else t
    t = transformType env poly (declAccess decl) $ declType decl
    v = transformExpression env $ valueValue decl
transformDeclaration _ env poly decl@DeclAbstract{}    = transformDeclarationAbstract env poly decl
transformDeclaration _ env poly decl@DeclCon{}         = transformDeclarationAbstract env poly decl
transformDeclaration _ env poly decl@DeclTypeSynonym{} = transformDeclarationAbstract env poly decl
transformDeclaration _ _ _ decl                        = decl

transformDeclarationAbstract :: SolvedConstraints -> Bool -> CoreDecl -> CoreDecl
transformDeclarationAbstract env poly decl = decl{declType = transformType env poly (declAccess decl) $ declType decl}

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Bool -> Access -> Type -> Type
transformType env poly acc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      -- If the function is exported and we're not in the last argument, we have to set applicativeess to L
      export = (arityFromType t2 /= 0) && accessPublic acc
      a1' = lookupVar a1 env poly export
      r' = lookupVar r env poly False
      a2' = lookupVar a2 env poly export
      t1' = TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') (transformType env poly acc t1)))
      t2' = transformType env poly acc t2
transformType env poly acc (TStrict t) = TStrict $ transformType env poly acc t
transformType env poly acc (TForall q k t) = TForall q k $ transformType env poly acc t
transformType _ _ _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> Expr -> Expr
-- Recursive has to stay recursive, bo transformation possible
transformExpression env (Let (Rec b) e) = Let (Rec (map (transformBind env) b)) $ transformExpression env e
-- Turn bind to strict if annotated with S
transformExpression env (Let (NonRec b@(Bind (Variable _ (TAp (TAnn a) (TAp (TAnn r) _))) _)) e) = Let binds $ transformExpression env e 
  where
    binds = if lookupVarPoly r env == S && lookupVarPoly a env == S then Strict bind else NonRec bind
    bind  = transformBind env b
-- Bind is already strict
transformExpression env (Let (Strict b) e) = Let (Strict (transformBind env b)) $ transformExpression env e
transformExpression env (Match i alts) = Match i $ map (transformAlt env) alts
transformExpression env (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (ApType e t) = ApType (transformExpression env e) (typeRemoveAnnotations t)
transformExpression env (Lam s (Variable x (TAp (TAnn a) (TAp (TAnn r) (TAp _ t)))) e) = Lam (s || s') (Variable x t') e' 
  where
    -- Check if annotation variable is S
    a' = lookupVarPoly a env
    r' = lookupVarPoly r env
    -- Lam can be made strict if it is strict when fully applied, i.e. when a' becomes S
    s' = uncontain (getVariablesAnn a') r' == S
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
transformBind env (Bind (Variable x (TAp _ (TAp _ (TAp _ t)))) e) = Bind (Variable x t') e'
  where
    t' = typeRemoveAnnotations t
    e' = transformExpression env e

-- Lookup annotation of variables
lookupVar :: SAnn -> SolvedConstraints -> Bool -> Bool -> SAnn
lookupVar ann env True  _      = lookupVarPoly ann env
lookupVar ann env False export = lookupVarMono ann env export

lookupVarPoly :: SAnn -> SolvedConstraints -> SAnn
lookupVarPoly (AnnVar x) env | elemMap x env = findMap x env
lookupVarPoly x _ = x

lookupVarMono :: SAnn -> SolvedConstraints -> Bool -> SAnn
lookupVarMono (AnnVar x) env export | elemMap x env = case findMap x env of
  S -> if export then L else S
  _ -> L
lookupVarMono S _ _ = S
lookupVarMono _ _ _ = L

uncontain :: [Id] -> SAnn -> SAnn
uncontain xs (AnnVar x) | x `elem` xs = S
uncontain xs (Join x y) = join (uncontain xs x) (uncontain xs y)
uncontain xs (Meet x y) = meet (uncontain xs x) (uncontain xs y)
uncontain _  x          = x
