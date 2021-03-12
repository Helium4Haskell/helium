module Helium.CodeGeneration.Core.Strictness.Annotate (annotateModule) where

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- Annotate module
annotateModule :: NameSupply -> CoreModule -> CoreModule
annotateModule supply mod = mod{moduleDecls = mapWithSupply annotateDeclaration supply $ moduleDecls mod}

-- Annotate declaration
annotateDeclaration :: NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration supply (DeclValue n a m t v c) = DeclValue n a m t' v' c
  where
    (supply1, supply2) = splitNameSupply supply
    t' = annotateType supply1 t
    v' = annotateExpression supply2 v
annotateDeclaration _ d = d

-- Annotate type
annotateType :: NameSupply -> Type -> Type
annotateType supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    where
        -- Annotate only on function arrows
        (id, supply') = freshId supply
        t1' = TAnn (AnnVar id) t1
        t2' = annotateType supply' t2
annotateType supply (TForall q k t) = TForall q k $ annotateType supply t
annotateType supply (TStrict t)     = TStrict $ annotateType supply t
annotateType _ t = t

-- Annotate expression
annotateExpression :: NameSupply -> Expr -> Expr
annotateExpression supply (Let b e) = Let b' e' 
  where
    (supply1, supply2) = splitNameSupply supply
    b' = annotateBinds supply1 b
    e' = annotateExpression  supply2 e
annotateExpression supply (Match x a) = Match x $ mapWithSupply annotateAlt supply a
annotateExpression supply (Ap e1 e2) = Ap e1' e2'
  where
    (supply1, supply2) = splitNameSupply supply
    e1' = annotateExpression supply1 e1
    e2' = annotateExpression supply2 e2
annotateExpression supply (ApType e t) = ApType (annotateExpression supply e) t
annotateExpression supply (Lam s (Variable x t) e) = Lam s (Variable x t') e'
  where
    (id, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'
    t' = TAnn (AnnVar id) $ annotateType supply1 t
    e' = annotateExpression supply2 e
annotateExpression supply (Forall q k e) = Forall q k $ annotateExpression supply e
annotateExpression _ expr = expr

-- Annotate binds
annotateBinds :: NameSupply -> Binds -> Binds
annotateBinds supply (Strict b) = Strict $               annotateBind supply b
annotateBinds supply (NonRec b) = NonRec $               annotateBind supply b
annotateBinds supply (Rec b)    = Rec    $ mapWithSupply annotateBind supply b

-- Annotate bind
annotateBind :: NameSupply -> Bind -> Bind
annotateBind supply (Bind (Variable x t) e) = Bind (Variable x t') e'
  where
    (id, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'
    t' = TAnn (AnnVar id) $ annotateType supply1 t
    e' = annotateExpression supply2 e

-- Annotate alt
annotateAlt :: NameSupply -> Alt -> Alt
annotateAlt supply (Alt p e) = Alt p $ annotateExpression supply e