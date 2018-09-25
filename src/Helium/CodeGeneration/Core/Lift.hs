{-| Module      :  Lift
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Lift lambdas and non-strict let declarations to toplevel.
-- Transforms the program such that all non-strict let declarations have a function application as binding.
-- We do so by adding new toplevel functions for those let declarations.
-- Furthermore we apply lambda lifting; all lambda expressions will be moved to toplevel declarations.
--
-- Before:
-- foo z =
--   let x = (let y! = f z in f y)
--   in f x
-- After:
-- bar z = let y! = f z in f y
-- foo z = let x = bar z in f x
--
-- Assumes that the AST is normalized, eg. the Normalize pass should be executed before.

module Helium.CodeGeneration.Core.Lift (coreLift) where

import Lvm.Common.Id
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Utils

coreLift :: NameSupply -> CoreModule -> CoreModule
coreLift supply (Module name major minor decls) = Module name major minor decls'
  where
    decls' = concat $ mapWithSupply liftExprInDecl supply decls

boundVar :: Bind -> Id
boundVar (Bind x _) = x

liftExprInDecl :: NameSupply -> CoreDecl -> ([CoreDecl])
liftExprInDecl supply (DeclValue name access enc expr customs) = DeclValue name access enc expr' customs : decls
  where
    (expr', decls) = liftExprIgnoreLambdas supply [] expr 
liftExprInDecl _ decl = [decl]

liftExprIgnoreLambdas :: NameSupply -> [Id] -> Expr -> (Expr, [CoreDecl])
liftExprIgnoreLambdas supply scope (Lam x expr) = (Lam x expr', decls)
  where
    (expr', decls) = liftExprIgnoreLambdas supply (x : scope) expr
liftExprIgnoreLambdas supply scope expr = liftExpr supply scope expr

liftExpr :: NameSupply -> [Id] -> Expr -> (Expr, [CoreDecl])
liftExpr supply scope (Let (Strict b) e) = (Let (Strict b') e', decls1 ++ decls2)
  where
    (supply1, supply2) = splitNameSupply supply
    (b', decls1) = strictBind supply1 scope b
    (e', decls2) = liftExpr supply2 (boundVar b : scope) e
liftExpr supply scope (Let (NonRec b) e) = (Let (NonRec b') e', decls1 ++ decls2)
  where
    (supply1, supply2) = splitNameSupply supply
    (b', decls1) = lazyBind supply1 scope b
    (e', decls2) = liftExpr supply2 (boundVar b : scope) e
liftExpr supply scope (Let (Rec bs) e) = (Let (Rec bs') e', concat decls1 ++ decls2)
  where
    scope' = map boundVar bs ++ scope
    (supply1, supply2) = splitNameSupply supply
    (bs', decls1) = unzip $ mapWithSupply (`lazyBind` scope') supply1 bs
    (e', decls2) = liftExpr supply2 scope' e
liftExpr supply scope (Match name alts) = (Match name alts', concat decls)
  where
    (alts', decls) = unzip $ mapWithSupply (`liftAlt` scope) supply alts
liftExpr supply scope (Lam x expr) = (Lam x expr', decls)
  where
    (expr', decls) = liftExpr supply (x : scope) expr
-- After normalization the other expression constructors cannot have let bindings
-- as subexpressions, so we can ignore them.
liftExpr supply scope expr = (expr, [])

strictBind :: NameSupply -> [Id] -> Bind -> (Bind, [CoreDecl])
strictBind supply scope b@(Bind _ (Lam _ _)) = lazyBind supply scope b
strictBind supply scope (Bind x expr) = (Bind x expr', decls)
  where
    (expr', decls) = liftExpr supply scope expr

lazyBind :: NameSupply -> [Id] -> Bind -> (Bind, [CoreDecl])
lazyBind supply scope (Bind x expr) = (Bind x ap, decl : decls)
  where
    ap = foldl (\e arg -> Ap e (Var arg)) (Var name) scope -- TODO: foldl vs foldr, Ap vs flip Ap?
    (name, supply') = freshId supply
    (expr', decls) = liftExpr supply' scope expr
    value = foldr Lam expr' scope
    decl :: CoreDecl
    decl = DeclValue
      { declName = name
      , declAccess = Defined False
      , valueEnc = Nothing -- TODO: What is valueEnc?
      , valueValue = value
      , declCustoms = []
      }

liftAlt :: NameSupply -> [Id] -> Alt -> (Alt, [CoreDecl])
liftAlt supply scope (Alt pat expr) = (Alt pat expr', decls)
  where
    (expr', decls) = liftExpr supply (newVars ++ scope) expr
    newVars = case pat of
      PatCon _ ids -> ids
      _ -> []


