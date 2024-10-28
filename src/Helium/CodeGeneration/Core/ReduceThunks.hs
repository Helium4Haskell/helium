{-| Module      :  ReduceThunks
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Reduces the number of thunks that are (will be) created.
-- It does so by evaluating 'cheap' expressions strictly. For instance, a literal
-- or a constructor can be evaluated strict, without changing the semantics

module Helium.CodeGeneration.Core.ReduceThunks (coreReduceThunks, isCheap) where

import Helium.Lvm.Common.Id
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Module

coreReduceThunks :: CoreModule -> CoreModule
coreReduceThunks = fmap reduceThunksInExpr

reduceThunksInExpr :: Expr -> Expr
reduceThunksInExpr (Let (NonRec b@(Bind var value)) expr)
  | isCheap value' = Let (Strict (Bind var value')) $ reduceThunksInExpr expr
  | otherwise      = Let (NonRec (Bind var value')) $ reduceThunksInExpr expr
  where
    value' = reduceThunksInExpr value
reduceThunksInExpr (Let (Strict b) expr) = Let (Strict $ reduceThunksInBind b) $ reduceThunksInExpr expr
reduceThunksInExpr (Let (Rec bs) expr) = Let (Rec $ map reduceThunksInBind bs) $ reduceThunksInExpr expr
reduceThunksInExpr (Match name alts) = Match name $ map reduceThunksInAlt alts
reduceThunksInExpr (Ap e1 e2) = Ap (reduceThunksInExpr e1) (reduceThunksInExpr e2)
reduceThunksInExpr (Lam strict var expr) = Lam strict var $ reduceThunksInExpr expr
reduceThunksInExpr (Forall x k expr) = Forall x k $ reduceThunksInExpr expr
reduceThunksInExpr (ApType e t) = ApType (reduceThunksInExpr e) t
reduceThunksInExpr expr = expr

reduceThunksInBind :: Bind -> Bind
reduceThunksInBind (Bind var value) = Bind var $ reduceThunksInExpr value

reduceThunksInAlt :: Alt -> Alt
reduceThunksInAlt (Alt pat expr) = Alt pat $ reduceThunksInExpr expr

isCheap :: Expr -> Bool
isCheap (Lit _) = True
-- A constructor (or applied constructor) is cheap
isCheap (Ap l _) = isCheap l
isCheap (Con _) = True
-- A let expression is cheap if its expression is cheap
-- and (the binding is lazy or its value is cheap)
isCheap (Let (Strict (Bind _ value)) expr) = isCheap value && isCheap expr
isCheap (Let _ expr) = isCheap expr
-- A call to "$primPackedToString" is cheap
isCheap (Var name) = name == idFromString "$primPackedToString"
isCheap (Forall _ _ e) = isCheap e
isCheap (ApType e _) = isCheap e
isCheap _ = False
