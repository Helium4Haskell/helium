{-| Module      :  RemoveAliases
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Removes variable aliassing, for lazy let bindings.
-- Before: let x = y in f x
-- After:  f y

module Helium.CodeGeneration.Core.RemoveAliases (coreRemoveAliases) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Data.Maybe(fromMaybe)
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Utils(mapAlts, mapBinds)

coreRemoveAliases :: CoreModule -> CoreModule
coreRemoveAliases = fmap (renameExpr emptyMap)

type Env = IdMap Id

lookupId :: Env -> Id -> Id
lookupId env x = fromMaybe x $ lookupMap x env 

renameExpr :: Env -> Expr -> Expr
renameExpr env (Let (NonRec (Bind x (Var y))) expr) = renameExpr (insertMap x (lookupId env y) env) expr
renameExpr env (Let bs expr) = Let (mapBinds (\x e -> Bind x $ renameExpr env e) bs) $ renameExpr env expr
renameExpr env (Match x alts) =
  Match (lookupId env x)
    $ mapAlts (\pat expr -> Alt pat $ renameExpr env expr) alts
renameExpr env (Ap e1 e2) = Ap (renameExpr env e1) (renameExpr env e2)
renameExpr env (Lam x expr) = Lam x $ renameExpr env expr
renameExpr env (Var x) = Var $ lookupId env x
renameExpr _ (Con con) = Con con
renameExpr _ (Lit lit) = Lit lit
