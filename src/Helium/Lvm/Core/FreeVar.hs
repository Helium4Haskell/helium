--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$
----------------------------------------------------------------
-- Calculate free variables
----------------------------------------------------------------
module Helium.Lvm.Core.FreeVar
   ( FreeVar(..)
   , Binder(..)
   )
where

import           Helium.Lvm.Common.IdSet
import           Helium.Lvm.Core.Expr

class FreeVar a where
   freeVar :: a -> IdSet

instance FreeVar a => FreeVar [a] where
   freeVar = unionSets . map freeVar

instance FreeVar Expr where
   freeVar expr = case expr of
      Let bs e -> freeVar bs `unionSet` (freeVar e `diffSet` binder bs)
      Match x  e                -> insertSet x (freeVar e)
      Ap    e1 e2               -> freeVar e1 `unionSet` freeVar e2
      Lam    _ (Variable x _) e -> deleteSet x (freeVar e)
      Forall _ _              e -> freeVar e
      ApType e _                -> freeVar e
      Con _                     -> emptySet
      Var x                     -> singleSet x
      Lit _                     -> emptySet

instance FreeVar Alt where
   freeVar (Alt p e) = freeVar e `diffSet` binder p

instance FreeVar Binds where
   freeVar binds = case binds of
      Rec    bs -> freeVar bs `diffSet` binder bs
      NonRec b  -> freeVar b
      Strict b  -> freeVar b

instance FreeVar Bind where
   freeVar (Bind _ e) = freeVar e -- non-recursive binder!

class Binder a where
   binder :: a -> IdSet

instance Binder a => Binder [a] where
   binder = unionSets . map binder

instance Binder Pat where
   binder (PatCon _ _ xs) = setFromList xs
   binder _               = emptySet

instance Binder Bind where
   binder (Bind (Variable x _) _) = singleSet x

instance Binder Binds where
   binder (Rec    bs) = binder bs
   binder (NonRec b ) = binder b
   binder (Strict b ) = binder b
