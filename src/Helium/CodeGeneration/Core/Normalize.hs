{-| Module      :  Normalize
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Adds let declarations for all non-trivial subexpressions (except the binding of a let expression and
-- the expression of an alternative in a match expression).
-- The target of a function application may also be an application or a constructor (eg, `f x y` is
-- allowed and is not rewritten to `let z = f x in z y`).
-- A lambda is also allowed in a lambda, to write multi-parameter functions.
--
-- Before: f (g x)
-- After: let y = g x in f y
--
-- Before: f (g (h x))
-- After: let y = (let z = h x in g z) in f y
--
-- A trivial expression is a variable.

module Helium.CodeGeneration.Core.Normalize (coreNormalize) where

import Lvm.Common.Id
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Utils

-- A trivial expression is a variable
isTrivial :: Expr -> Bool
isTrivial (Var _) = True
isTrivial _ = False

-- Valid targets for function applications are applications, constructors,
-- variables.
isApTarget :: Expr -> Bool
isApTarget (Ap _ _) = True
isApTarget (Con _) = True
isApTarget (Var _) = True
isApTarget (Forall _ _ e) = isApTarget e
isApTarget (ApType e _) = isApTarget e
isApTarget _ = False

coreNormalize :: NameSupply -> CoreModule -> CoreModule
coreNormalize supply m
  = mapExprWithSupply normalizeLambda supply m

-- Lambda expressions are allowed on toplevel, in a let binding and in a lambda.
-- Here we skip through all Lambda nodes until we find a non-lambda node,
-- which we will normalize.
normalizeLambda :: NameSupply -> Expr -> Expr
normalizeLambda supply (Lam var expr) = Lam var $ normalizeLambda supply expr
normalizeLambda supply (Forall x k expr) = Forall x k $ normalizeLambda supply expr
normalizeLambda supply expr = normalize supply expr

-- Normalizes an expression.
normalize :: NameSupply -> Expr -> Expr
normalize supply expr = addBindings expr' bindings
  where
    (expr', bindings) = normSubExprs supply expr

-- Normalizes an expression. Adds a new binding if the expression isn't a variable.
normExpr :: NameSupply -> Expr -> (Expr, [Bind])
normExpr supply expr
  | isTrivial expr' = (expr', bindings)
  | otherwise = (Var name, [Bind (Variable name TAny) $ addBindings expr' bindings])
  where
    (expr', bindings) = normSubExprs supply' expr
    (name, supply') = freshId supply

-- Normalizes the subexpressions of an expression
normSubExprs :: NameSupply -> Expr -> (Expr, [Bind])
normSubExprs supply (Let binds expr) = (Let (normBinds supply1 binds) $ normalize supply2 expr, [])
  where
    (supply1, supply2) = splitNameSupply supply
normSubExprs supply (Match x alts) = (Match x $ mapWithSupply normAlt supply alts, [])
normSubExprs supply (Ap e1 e2) = (Ap e1'' e2', bindings1' ++ bindings2)
  where
    (name, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'
    -- Normalize e1 to a variable or application
    (e1', bindings1) = normSubExprs supply1 e1
    (e1'', bindings1')
      | isApTarget e1' = (e1', bindings1)
      | otherwise = (Var name, [Bind (Variable name TAny) $ addBindings e1' bindings1])
    (e2', bindings2) = normExpr supply2 e2
normSubExprs supply (Lam var expr) = (Lam var $ normalizeLambda supply expr, [])
normSubExprs supply (Forall x k expr) = (Forall x k expr', binds)
  where
    (expr', binds) = normSubExprs supply expr
normSubExprs supply (ApType expr t) = (ApType expr' t, binds)
  where
    (expr', binds) = normSubExprs supply expr
normSubExprs supply expr = (expr, []) -- expr is already trivial, we don't need to normalize it further.

normBinds :: NameSupply -> Binds -> Binds
normBinds supply (Rec binds) = Rec $ mapWithSupply normBind supply binds
normBinds supply (Strict b) = Strict $ normBind supply b
normBinds supply (NonRec b) = NonRec $ normBind supply b

normBind :: NameSupply -> Bind -> Bind
normBind supply (Bind var expr) = Bind var $ normalize supply expr

normAlt :: NameSupply -> Alt -> Alt
normAlt supply (Alt p expr) = Alt p $ normalize supply expr

addBindings :: Expr -> [Bind] -> Expr
addBindings = foldl add
  where
    add :: Expr -> Bind -> Expr
    add expr b = Let (NonRec b) expr
