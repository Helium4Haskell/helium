module Helium.CodeGeneration.Core.Strictness.Annotate (annotateModule, annotateDeclaration) where

import Data.Maybe

import Helium.CodeGeneration.Core.Strictness.Data

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Annotate module
annotateModule :: NameSupply -> CoreModule -> CoreModule
annotateModule supply mod = mod{moduleDecls = mapWithSupply annotateDeclaration supply (moduleDecls mod)}

-- Annotate declaration
annotateDeclaration :: NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration supply decl@DeclValue{} = decl{declType = t, valueValue = v}
  where
    (supply1, supply2) = splitNameSupply supply
    t = annotateType supply1 $ declType decl
    v = annotateExpression supply2 $ valueValue decl
annotateDeclaration supply decl@DeclAbstract{} = annotateDeclType supply decl
annotateDeclaration supply decl@DeclCon{} = annotateDeclType supply decl
annotateDeclaration supply decl@DeclTypeSynonym{} = annotateDeclType supply decl
annotateDeclaration _ decl = decl

annotateDeclType :: NameSupply -> CoreDecl -> CoreDecl
annotateDeclType supply decl = decl{declType = t}
  where
    t = if hasCustomAnn (declCustoms decl) then fromCustomAnn (declCustoms decl) else annotateType supply $ declType decl

-- Annotate type
annotateType :: NameSupply -> Type -> Type
annotateType supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    where
      -- Annotate only on function arrows
      (id1, id2, id3, supply') = threeIds supply
      (supply1, supply2) = splitNameSupply supply'
      ann1 = if typeIsStrict t1 then S else AnnVar id1
      ann2 = if typeIsStrict t1 then S else AnnVar id2
      t1' = TAnn (ann1, ann2, AnnVar id3) $ annotateType supply1 t1
      t2' = annotateType supply2 t2
annotateType supply (TForall q k t) = TForall q k $ annotateType supply t
annotateType supply (TStrict t)     = TStrict $ annotateType supply t
annotateType _      t               = t

-- Annotate expression
annotateExpression :: NameSupply -> Expr -> Expr
annotateExpression supply (Let b e) = Let b' e'
  where
    (supply1, supply2) = splitNameSupply supply
    b' = annotateBinds      supply1 b
    e' = annotateExpression supply2 e
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
annotateExpression _ e = e -- Con, Lit and Var

-- Annotate binds
annotateBinds :: NameSupply -> Binds -> Binds
annotateBinds supply (Strict b) = Strict $ annotateBind True supply b
annotateBinds supply (NonRec b) = NonRec $ annotateBind False supply b         
annotateBinds supply (Rec b)    = Rec $ mapWithSupply (annotateBind False) supply b

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
annotatePat supply (PatCon c t i) = PatCon c (mapWithSupply annotateType supply t) i
annotatePat _ p = p

-- Annotate lambda or binding
annotateLamOrBind :: Bool -> NameSupply -> Variable -> Expr -> (Variable, Expr)
annotateLamOrBind strict supply (Variable x t) e = (Variable x t', e')
  where
    (id1, id2, id3, supply') = threeIds supply
    (supply1, supply2) = splitNameSupply supply'
    ann1 = if strict then S else AnnVar id1
    ann2 = if strict then S else AnnVar id2
    t' = TAnn (ann1, ann2, AnnVar id3) $ annotateType supply1 t
    e' = annotateExpression supply2 e

threeIds :: NameSupply -> (Id, Id, Id, NameSupply)
threeIds supply0 = (id1, id2, id3, supply3)
  where
    (id1, supply1) = freshId supply0
    (id2, supply2) = freshId supply1
    (id3, supply3) = freshId supply2