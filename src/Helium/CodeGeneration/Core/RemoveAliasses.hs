{-| Module      :  RemoveAliasses
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Removes variable aliassing, for lazy let bindings.
-- Before: let x = y in f x
-- After:  f y

module Helium.CodeGeneration.Core.RemoveAliasses (coreRemoveAliasses) where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Data.Maybe(fromMaybe)
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Utils(mapAlts, mapBinds)

coreRemoveAliasses :: CoreModule -> CoreModule
coreRemoveAliasses = fmap (renameExpr emptyMap)

type Env = IdMap Id

renameExpr :: Env -> Expr -> Expr
renameExpr env (Let (NonRec (Bind x (Var y))) expr) = renameExpr (insertMap x y env) expr
renameExpr env (Let bs expr) = Let (mapBinds (\x e -> Bind x $ renameExpr env e) bs) expr
renameExpr env (Match x alts) =
  Match (fromMaybe x $ lookupMap x env)
    $ mapAlts (\pat expr -> Alt pat $ renameExpr env expr) alts
renameExpr env (Ap e1 e2) = Ap (renameExpr env e1) (renameExpr env e2)
renameExpr env (Lam x expr) = Lam x $ renameExpr env expr
renameExpr env (Var x) = Var $ fromMaybe x $ lookupMap x env
renameExpr _ expr = expr -- Literal or Constructor

{-
data Expr       = Let       !Binds Expr       
                | Match     !Id Alts
                | Ap        Expr Expr
                | Lam       !Id Expr
                | Con       !(Con Expr)
                | Var       !Id
				| Lit       !Literal
				-}