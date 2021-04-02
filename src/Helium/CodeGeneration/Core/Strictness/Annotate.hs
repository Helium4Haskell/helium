module Helium.CodeGeneration.Core.Strictness.Annotate (annotateModule) where

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- Annotate module
annotateModule :: NameSupply -> CoreModule -> CoreModule
annotateModule supply mod = mod{moduleDecls = mapWithSupply annotateDeclaration supply $ moduleDecls mod}

-- Annotate declaration, switch original and annotated type
annotateDeclaration :: NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration supply (DeclValue n a m t ta v c) = DeclValue n a m t' t v' c
  where
    (supply1, supply2) = splitNameSupply supply
    t' = annotateType supply1 ta
    v' = annotateExpression supply2 v
-- Switch arguments
annotateDeclaration _ (DeclAbstract n a m ar t ta c) = DeclAbstract n a m ar t' t c
  where
    t' = annotateTypeAbstract ta
annotateDeclaration _ (DeclCon n a m t f c) = DeclCon n a m t' f c
  where
    t' = annotateTypeAbstract t
annotateDeclaration _ (DeclTypeSynonym n a m s t c) = DeclTypeSynonym n a m s t' c
  where
    t' = annotateTypeAbstract t
annotateDeclaration _ d = d

-- Annotate type
annotateType :: NameSupply -> Type -> Type
annotateType supply (TAp (TAp (TCon TConFun) (TAnn a t1)) t2) = TAp (TAp (TCon TConFun) (TAnn a t1')) t2' 
  where
      -- Already annotated
      (supply1, supply2) = splitNameSupply supply
      t1' = annotateType supply1 t1
      t2' = annotateType supply2 t2
annotateType supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    where
      -- Annotate only on function arrows
      (id1, id2, id3, supply') = threeIds supply
      (supply1, supply2) = splitNameSupply supply'
      ann = case t1 of
        TStrict _ -> S
        _         -> AnnVar id2
      t1' = TAnn (AnnVar id1, ann, AnnVar id3) $ annotateType supply1 t1
      t2' = annotateType supply2 t2
annotateType supply (TForall q k t) = TForall q k $ annotateType supply t
annotateType supply (TStrict t)     = TStrict $ annotateType supply t
annotateType _ t = t

-- Cannot place variables because they won't be inferred due to no body, so assume L unless type is strict, then S
annotateTypeAbstract :: Type -> Type
annotateTypeAbstract (TAp (TAp (TCon TConFun) (TAnn a t1)) t2) = TAp (TAp (TCon TConFun) (TAnn a t1')) t2'
  where
    t1' = annotateTypeAbstract t1
    t2' = annotateTypeAbstract t2
annotateTypeAbstract (TAp (TAp (TCon TConFun) (TStrict t1)) t2) = TAp (TAp (TCon TConFun) (TAnn (L, S, L) t1')) t2'
  where
    t1' = TStrict $ annotateTypeAbstract t1
    t2' = annotateTypeAbstract t2
annotateTypeAbstract (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) (TAnn (L, L, L) t1')) t2'
  where
    t1' = annotateTypeAbstract t1
    t2' = annotateTypeAbstract t2
annotateTypeAbstract (TForall q k t) = TForall q k $ annotateTypeAbstract t
annotateTypeAbstract (TStrict t)     = TStrict $ annotateTypeAbstract t
annotateTypeAbstract t = t

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
annotateExpression supply (ApType e t) = ApType e' t'
  where
    (supply1, supply2) = splitNameSupply supply
    e' = annotateExpression supply1 e
    t' = annotateType supply2 t
annotateExpression supply (Lam strict v e) = Lam strict v' e'
  where
    (v', e') = annotateLamOrBind strict supply v e
annotateExpression supply (Forall q k e) = Forall q k $ annotateExpression supply e
annotateExpression _ (Con c) = Con c
annotateExpression _ (Lit l) = Lit l
annotateExpression _ (Var v) = Var v

-- Annotate binds
annotateBinds :: NameSupply -> Binds -> Binds
annotateBinds supply (Strict b) = Strict $                annotateBind True   supply b
annotateBinds supply (NonRec b) = NonRec $                annotateBind False  supply b
annotateBinds supply (Rec b)    = Rec    $ mapWithSupply (annotateBind False) supply b

-- Annotate bind
annotateBind :: Bool -> NameSupply -> Bind -> Bind
annotateBind strict supply (Bind v e) = Bind v' e'
  where
    (v', e') = annotateLamOrBind strict supply v e

-- Annotate alt
annotateAlt :: NameSupply -> Alt -> Alt
annotateAlt supply (Alt p e) = Alt p' e'
  where
    (supply1, supply2) = splitNameSupply supply
    p' = annotatePat supply1 p
    e' = annotateExpression supply2 e

-- Annotate pat
annotatePat :: NameSupply -> Pat -> Pat
annotatePat supply (PatCon c t i) = PatCon c t' i
  where
    t' = mapWithSupply annotateType supply t
annotatePat _ p = p

annotateLamOrBind :: Bool -> NameSupply -> Variable -> Expr -> (Variable, Expr)
annotateLamOrBind strict supply (Variable x t) e = (Variable x t', e')
  where
    (id1, id2, id3, supply') = threeIds supply
    ann = if strict then S else AnnVar id2
    (supply1, supply2) = splitNameSupply supply'
    t' = TAnn (AnnVar id1, ann, AnnVar id3) $ annotateType supply1 t
    e' = annotateExpression supply2 e

threeIds :: NameSupply -> (Id, Id, Id, NameSupply)
threeIds supply0 = (id1, id2, id3, supply3)
  where
    (id1, supply1) = freshId supply0
    (id2, supply2) = freshId supply1
    (id3, supply3) = freshId supply2