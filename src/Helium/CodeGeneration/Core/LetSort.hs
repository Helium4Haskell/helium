--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

----------------------------------------------------------------
-- Determine which bindings are really recursive and which are not.
-- maintains free variable information & normalised structure
----------------------------------------------------------------
module Helium.CodeGeneration.Core.LetSort (coreLetSort) where

import Data.Graph hiding (topSort)
import Data.Tree
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.FreeVar
import Helium.Lvm.Core.Utils
import Data.Maybe
import Control.Arrow (second)

----------------------------------------------------------------
-- coreLetSort
-- pre: [coreFreeVar] all let bindings are annotated with their free variables
--
-- transform a @Rec@ bindings into the smallest @NonRec@ and @Rec@ bindings.
----------------------------------------------------------------
coreLetSort :: CoreModule -> CoreModule
coreLetSort = fmap lsExpr

lsExpr :: Expr -> Expr
lsExpr expr
  = case expr of
      Let (Strict (Bind var rhs)) e
        -> Let (Strict (Bind var (lsExpr rhs))) (lsExpr e)
      Let binds e
        -> let bindss = sortBinds binds
           in foldr Let (lsExpr e) bindss
      Match x alts
        -> Match x (lsAlts alts)
      Lam strict x e
        -> Lam strict x (lsExpr e)
      Ap e1 e2
        -> Ap (lsExpr e1) (lsExpr e2)
      Forall x k e
        -> Forall x k $ lsExpr e
      ApType e t
        -> ApType (lsExpr e) t
      _
        -> expr

lsAlts :: Alts -> Alts
lsAlts = mapAlts (\pat -> Alt pat . lsExpr)

----------------------------------------------------------------
-- topological sort let bindings
----------------------------------------------------------------
sortBinds :: Binds -> [Binds]
sortBinds (Rec bindsrec)
  = let binds  = map (\(Bind (Variable x t) rhs) -> (x,(t, rhs))) bindsrec
        names  = zip (map fst binds) [0..]
        es     = concatMap (depends names) binds
        sorted = topSort (length names-1) es
        binds'  = map (map (binds!!)) sorted
        binds'' = map (map (\(x, (t, rhs)) -> (x, (t, lsExpr rhs)))) binds'
    in  map toBinding binds'' -- foldr sortLets (lsExpr expr) binds''
sortBinds binds
  = [mapBinds (\var expr -> Bind var (lsExpr expr)) binds]

-- topological sort
topSort :: Vertex -> [Edge] -> [[Vertex]]
topSort n = map flatten . scc . buildG (0, n)

toBinding :: [(Id, (Type, Expr))] -> Binds
toBinding [(x, (t, rhs))]
  | not (elemSet x (freeVar rhs)) = NonRec (Bind (Variable x t) rhs)
toBinding binds
  = Rec (map (\(x, (t, rhs)) -> Bind (Variable x t) rhs) binds)

depends :: [(Id, Vertex)] -> (Id, (Type, Expr)) -> [(Vertex,Vertex)]
depends names (v, (_, expr))
  = foldSet depend [] (freeVar expr)
  where
    index = fromMaybe (error msg) (lookup v names)
    msg   = "CoreLetSort.depends: id not in let group??"
    depend x ds   = case lookup x names of
                      Just i  -> (index,i):ds
                      Nothing -> ds
