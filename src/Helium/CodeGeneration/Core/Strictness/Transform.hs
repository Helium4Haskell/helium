module Helium.CodeGeneration.Core.Strictness.Transform (transformModule, transformDeclaration, transformType, transformExpression) where

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Apply strict annotations on module
transformModule :: SolvedConstraints -> Bool -> CoreModule -> CoreModule
transformModule sc poly mod = mod{moduleDecls = map (transformDeclaration sc poly) (moduleDecls mod)}

-- Apply strict annotations on declarations
transformDeclaration :: SolvedConstraints -> Bool -> CoreDecl -> CoreDecl
transformDeclaration sc poly decl@DeclValue{} = decl{declType = t', valueValue = v}
  where
    v = transformExpression sc $ valueValue decl
    t = transformType sc poly (accessPublic $ declAccess decl) $ declType decl
    t' = if poly then forallify True t else t
transformDeclaration sc poly decl@DeclAbstract{}    = transformDeclarationAbstract sc poly decl
transformDeclaration sc poly decl@DeclCon{}         = transformDeclarationAbstract sc poly decl
transformDeclaration sc poly decl@DeclTypeSynonym{} = transformDeclarationAbstract sc poly decl
transformDeclaration _ _ decl                       = decl

transformDeclarationAbstract :: SolvedConstraints -> Bool -> CoreDecl -> CoreDecl
transformDeclarationAbstract sc poly decl = decl{declType = transformType sc poly (accessPublic $ declAccess decl) $ declType decl}

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Bool -> Bool -> Type -> Type
transformType sc poly acc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      -- If the function is exported and we're not in the last argument, we have to set applicativeess to L
      export = (arityFromType t2 /= 0) && acc
      a1' = lookupVar a1 sc poly export
      r' = lookupVar r sc poly False
      a2' = lookupVar a2 sc poly export
      t1' = TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') (transformType sc poly acc t1)))
      t2' = transformType sc poly acc t2
transformType sc poly acc (TAp t1 t2) = TAp (transformType sc poly acc t1) (transformType sc poly acc t2)
transformType sc poly _ (TAnn a) = TAnn $ lookupVar a sc poly False
transformType sc poly acc (TStrict t) = transformType sc poly acc t
transformType sc poly acc (TForall q k t) = TForall q k $ transformType sc poly acc t
transformType _ _ _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> Expr -> Expr
-- Recursive has to stay recursive, bo transformation possible
transformExpression sc (Let b e) = Let (transformBinds sc b) $ transformExpression sc e
transformExpression sc (Match i alts) = Match i $ map (transformAlt sc) alts
transformExpression sc (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression sc e1
    e2' = transformExpression sc e2
transformExpression sc (ApType e t) = case t of
  TAnn _ -> transformExpression sc e
  _      -> ApType (transformExpression sc e) (typeRemoveAnnotations t)
transformExpression sc (Lam s (Variable x (TAp (TAnn a) (TAp (TAnn r) (TAp _ t)))) e) = Lam (s || s') (Variable x t') e' 
  where
    -- Lookup variables, polyvariant search because we need to check if it is not L
    a' = lookupVarPoly a sc
    r' = lookupVarPoly r sc
    -- Lam can be made strict if it is strict when fully applied, i.e. when a' becomes S
    s' = uncontain (getVariablesAnn a') r' == S
    e' = transformExpression sc e
    t' = typeRemoveAnnotations t
transformExpression sc (Forall q k e) = Forall q k $ transformExpression sc e
transformExpression _ e = e -- Con, Lit and Var

-- Apply strict transformations on binds
transformBinds :: SolvedConstraints -> Binds -> Binds
transformBinds sc (Strict b) = Strict $ transformBind sc b
transformBinds sc (NonRec b) = if bindToStrict sc b then Strict b' else NonRec b'
  where
    b' = transformBind sc b
transformBinds sc (Rec bs) = Rec $ map (transformBind sc) bs

-- Apply strict annotations on bind
transformBind :: SolvedConstraints -> Bind -> Bind
transformBind sc (Bind (Variable x (TAp _ (TAp _ (TAp _ t)))) e) = Bind (Variable x t') e'
  where
    t' = typeRemoveAnnotations t
    e' = transformExpression sc e

-- Apply strict transformations on alts
transformAlt :: SolvedConstraints -> Alt -> Alt
transformAlt sc (Alt p e) = Alt p' e'
  where
    p' = transformPat p
    e' = transformExpression sc e

-- Apply strict transformations on pats
transformPat :: Pat -> Pat
transformPat (PatCon c t i) = PatCon c (map typeRemoveAnnotations $ removeAnn t) i
transformPat p = p

removeAnn :: [Type] -> [Type]
removeAnn (TAnn _:xs) = removeAnn xs
removeAnn x = x

-- Lookup annotation of variables
lookupVar :: SAnn -> SolvedConstraints -> Bool -> Bool -> SAnn
lookupVar ann sc True  _      = lookupVarPoly ann sc
lookupVar ann sc False export = lookupVarMono ann sc export

lookupVarPoly :: SAnn -> SolvedConstraints -> SAnn
lookupVarPoly (AnnVar x) sc | elemMap x sc = findMap x sc
lookupVarPoly x _ = x

lookupVarMono :: SAnn -> SolvedConstraints -> Bool -> SAnn
lookupVarMono (AnnVar x) sc export | elemMap x sc = case findMap x sc of
  S -> if export then L else S
  _ -> L
lookupVarMono S _ _ = S
lookupVarMono _ _ _ = L

uncontain :: [Id] -> SAnn -> SAnn
uncontain xs (AnnVar x) | x `elem` xs = S
uncontain xs (Join x y) = join (uncontain xs x) (uncontain xs y)
uncontain xs (Meet x y) = meet (uncontain xs x) (uncontain xs y)
uncontain _  x          = x

-- Turn bind to strict if annotated with S
bindToStrict :: SolvedConstraints -> Bind -> Bool
bindToStrict sc (Bind (Variable _ (TAp (TAnn a) (TAp (TAnn r) (TAp _ _)))) _) = lookupVarPoly r sc == S && lookupVarPoly a sc == S
