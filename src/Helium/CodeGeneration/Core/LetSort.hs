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
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.FreeVar
import Lvm.Core.Utils
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
      Let (Strict (Bind x rhs)) e
        -> Let (Strict (Bind x (lsExpr rhs))) (lsExpr e)
      Let binds e
        -> let bindss = sortBinds binds
           in foldr Let (lsExpr e) bindss
      Match x alts
        -> Match x (lsAlts alts)
      Lam x e
        -> Lam x (lsExpr e)
      Ap e1 e2
        -> Ap (lsExpr e1) (lsExpr e2)
      Con (ConTag tag arity)
        -> Con (ConTag (lsExpr tag) arity)
      _
        -> expr

lsAlts :: Alts -> Alts
lsAlts = mapAlts (\pat -> Alt pat . lsExpr)

----------------------------------------------------------------
-- topological sort let bindings
----------------------------------------------------------------
sortBinds :: Binds -> [Binds]
sortBinds (Rec bindsrec)
  = let binds  = map (\(Bind x rhs) -> (x,rhs)) bindsrec
        names  = zip (map fst binds) [0..]
        es     = concatMap (depends names) binds
        sorted = topSort (length names-1) es
        binds'  = map (map (binds!!)) sorted
        binds'' = map (map (second lsExpr)) binds'
    in  map toBinding binds'' -- foldr sortLets (lsExpr expr) binds''
sortBinds binds
  = [mapBinds (\x expr -> Bind x (lsExpr expr)) binds]

-- topological sort
topSort :: Vertex -> [Edge] -> [[Vertex]]
topSort n = map flatten . scc . buildG (0, n)

toBinding :: [(Id, Expr)] -> Binds
toBinding [(x,rhs)]
  | not (elemSet x (freeVar rhs)) = NonRec (Bind x rhs)
toBinding binds
  = Rec (map (uncurry Bind) binds)

depends :: [(Id,Vertex)] -> (Id,Expr) -> [(Vertex,Vertex)]
depends names (v,expr)
  = foldSet depend [] (freeVar expr)
  where
    index = fromMaybe (error msg) (lookup v names)
    msg   = "CoreLetSort.depends: id not in let group??"
    depend x ds   = case lookup x names of
                      Just i  -> (index,i):ds
                      Nothing -> ds
