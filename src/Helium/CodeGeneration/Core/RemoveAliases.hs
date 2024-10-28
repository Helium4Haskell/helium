{-| Module      :  RemoveAliases
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Removes variable aliassing.
-- Lazy let binds of the form `let x = y in expr` are removed, by subsituting x with y in `expr`.
-- Before: let x = y in f x
-- After:  f y
--
-- Strict let binds of the form `let! x = y in expr` are removed in the same way, if `y` was already evaluated strict.
--
-- Match statements on the same variable are flattened: if an alternative of a branch / alternative is a
-- match expression on the same scrutinee and the pattern of the branch is a default pattern, then the alternatives
-- of the inner match will be inlined in the outer match.
-- Before:
-- match x on
--   as
--   _ -> match x on
--     bs
-- 
-- After:
-- match x on
--   as
--   bs

module Helium.CodeGeneration.Core.RemoveAliases (coreRemoveAliases) where

import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Common.IdMap
import Data.Maybe(fromMaybe)
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.Module
import Helium.Lvm.Core.Utils(mapAlts, mapBinds)

coreRemoveAliases :: CoreModule -> CoreModule
coreRemoveAliases = fmap (renameExpr emptyEnv)

data Env = Env !IdSet !(IdMap Id)

emptyEnv :: Env
emptyEnv = Env emptySet emptyMap

lookupId :: Env -> Id -> Id
lookupId (Env _ mapping) x = fromMaybe x $ lookupMap x mapping

insertId :: Id -> Id -> Env -> Env
insertId x y (Env stricts mapping) = Env stricts (insertMap x y mapping)

insertStrict :: Id -> Env -> Env
insertStrict x (Env stricts mapping) = Env (insertSet x stricts) mapping

isStrict :: Env -> Id -> Bool
isStrict (Env stricts _) x = x `elemSet` stricts

renameExpr :: Env -> Expr -> Expr
renameExpr env (Let (NonRec (Bind (Variable x _) (Var y))) expr) = renameExpr (insertId x (lookupId env y) env) expr
renameExpr env (Let (Strict (Bind var@(Variable x _) bindExpr)) expr) = bind $ renameExpr (insertStrict x env') expr
  where
    (bind, env') = case bindExpr of
      Var y
        | isStrict env y -> (id, insertId x (lookupId env y) env)
      _ -> (Let $ Strict $ Bind var $ renameExpr env bindExpr, env)
renameExpr env (Let bs expr) = Let (mapBinds (\var e -> Bind var $ renameExpr env e) bs) $ renameExpr env expr
renameExpr env (Match x alts) =
  Match x'
    $ alts >>= renameAlt env x'
  where
    x' = lookupId env x
renameExpr env (Ap e1 e2) = Ap (renameExpr env e1) (renameExpr env e2)
renameExpr env (Lam strict var@(Variable x tp) expr) = Lam strict var $ renameExpr env' expr
  where
    env'
      | typeIsStrict tp = insertStrict x env
      | otherwise = env
renameExpr env (Var x) = Var $ lookupId env x
renameExpr _ (Con con) = Con con
renameExpr _ (Lit lit) = Lit lit
renameExpr env (Forall x k expr) = Forall x k $ renameExpr env expr
renameExpr env (ApType expr t) = ApType (renameExpr env expr) t

renameAlt :: Env -> Id -> Alt -> [Alt]
renameAlt env scrutinee (Alt pat expr) = case (pat, expr') of
  (PatDefault, Match x alts)
    | scrutinee == x -> alts
  _ -> [Alt pat expr']
  where
    expr' = renameExpr env expr
