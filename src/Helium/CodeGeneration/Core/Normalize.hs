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

import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.Utils
import Helium.CodeGeneration.Core.TypeEnvironment

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
isApTarget (Forall _ _ e) = False
isApTarget (ApType e _) = isApTarget e
isApTarget _ = False

coreNormalize :: NameSupply -> CoreModule -> CoreModule
coreNormalize supply m
  = mapExprWithSupply (`normalizeLambda` env) supply m
  where
    env = typeEnvForModule m

-- Lambda expressions are allowed on toplevel, in a let binding and in a lambda.
-- Here we skip through all Lambda nodes until we find a non-lambda node,
-- which we will normalize.
normalizeLambda :: NameSupply -> TypeEnvironment -> Expr -> Expr
normalizeLambda supply env (Lam strict var expr) = Lam strict var $ normalizeLambda supply env' expr
  where
    env' = typeEnvAddVariable var env
normalizeLambda supply env (Forall x k expr) = Forall x k $ normalizeLambda supply env expr
normalizeLambda supply env expr = normalize supply env expr

-- Normalizes an expression.
normalize :: NameSupply -> TypeEnvironment -> Expr -> Expr
normalize supply env expr = addBindings expr' bindings
  where
    (expr', bindings) = normSubExprs supply env expr

-- Normalizes an expression. Adds a new binding if the expression isn't a variable.
normExpr :: NameSupply -> TypeEnvironment -> Expr -> (Expr, [Bind])
normExpr supply env expr
  | isTrivial expr' = (expr', bindings)
  | otherwise = (Var name, [Bind (Variable name $ typeOfCoreExpression env expr) $ addBindings expr' bindings])
  where
    (expr', bindings) = normSubExprs supply' env expr
    (name, supply') = freshId supply

-- Normalizes the subexpressions of an expression
normSubExprs :: NameSupply -> TypeEnvironment -> Expr -> (Expr, [Bind])
normSubExprs supply env (Let binds expr) = (Let binds' $ normalize supply2 env' expr, [])
  where
    (supply1, supply2) = splitNameSupply supply
    (env', binds') = normBinds supply1 env binds
normSubExprs supply env (Match x alts) = (Match x $ mapWithSupply (`normAlt` env) supply alts, [])
normSubExprs supply env (Ap e1 e2) = (Ap e1'' e2', bindings1' ++ bindings2)
  where
    (name, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'
    -- Normalize e1 to a variable or application
    (e1', bindings1) = normSubExprs supply1 env e1
    (e1'', bindings1')
      | isApTarget e1' = (e1', bindings1)
      | otherwise = (Var name, [Bind (Variable name $ typeOfCoreExpression env e1) $ addBindings e1' bindings1])
    (e2', bindings2) = normExpr supply2 env e2
normSubExprs supply env expr@(Lam _ _ _) = (normalizeLambda supply env expr, [])
normSubExprs supply env expr@(Forall _ _ _) = (normalizeLambda supply env expr, [])
normSubExprs supply env (ApType expr t) = (ApType expr'' t, bindings')
  where
    (name, supply') = freshId supply
    (expr', bindings) = normSubExprs supply' env expr
    (expr'', bindings')
      | isApTarget expr' = (expr', bindings)
      | otherwise = (Var name, [Bind (Variable name $ typeOfCoreExpression env expr') $ addBindings expr' bindings])
normSubExprs supply env expr = (expr, []) -- expr is already trivial, we don't need to normalize it further.

normBinds :: NameSupply -> TypeEnvironment -> Binds -> (TypeEnvironment, Binds)
normBinds supply env (Rec binds) = (env, Rec $ mapWithSupply (`normBind` env') supply binds)
  where
    env' = typeEnvAddBinds (Rec binds) env
normBinds supply env (Strict b) = (env', Strict $ normBind supply env b)
  where
    env' = typeEnvAddBind b env
normBinds supply env (NonRec b) = (env', NonRec $ normBind supply env b)
  where
    env' = typeEnvAddBind b env

normBind :: NameSupply -> TypeEnvironment -> Bind -> Bind
normBind supply env (Bind var expr) = Bind var $ normalize supply env expr

normAlt :: NameSupply -> TypeEnvironment -> Alt -> Alt
normAlt supply env (Alt p expr) = Alt p $ normalize supply env' expr
  where
    env' = typeEnvAddPattern p env

addBindings :: Expr -> [Bind] -> Expr
addBindings = foldl add
  where
    add :: Expr -> Bind -> Expr
    add expr b = Let (NonRec b) expr
