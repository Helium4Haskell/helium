--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id: Data.hs 250 2012-08-22 10:59:40Z bastiaan $

module Helium.Lvm.Core.Utils
  ( module Helium.Lvm.Core.Module
  , listFromBinds
  , mapBinds
  , mapAccumBinds
  , zipBindsWith
  , mapAlts
  , zipAltsWith
  , mapExprWithSupply
  , mapAccum
  , createFunction
  )
where

import           Helium.Lvm.Core.Expr
import           Helium.Lvm.Core.Type
import           Helium.Lvm.Common.Id
import           Helium.Lvm.Core.Module

----------------------------------------------------------------
-- Binders functions
----------------------------------------------------------------

listFromBinds :: Binds -> [Bind]
listFromBinds binds = case binds of
  NonRec bind -> [bind]
  Strict bind -> [bind]
  Rec    recs -> recs

mapBinds :: (Variable -> Expr -> Bind) -> Binds -> Binds
mapBinds f binds = case binds of
  NonRec (Bind var rhs) -> NonRec (f var rhs)
  Strict (Bind var rhs) -> Strict (f var rhs)
  Rec    recs           -> Rec (map (\(Bind var rhs) -> f var rhs) recs)

mapAccumBinds
  :: (a -> Variable -> Expr -> (Bind, a)) -> a -> Binds -> (Binds, a)
mapAccumBinds f x binds = case binds of
  NonRec (Bind var rhs) -> let (bind, z) = f x var rhs in (NonRec bind, z)
  Strict (Bind var rhs) -> let (bind, z) = f x var rhs in (Strict bind, z)
  Rec recs ->
    let (recs', z) = mapAccum (\a (Bind var rhs) -> f a var rhs) x recs
    in  (Rec recs', z)

mapAccum :: (a -> b -> (c, a)) -> a -> [b] -> ([c], a)
mapAccum _ s []       = ([], s)
mapAccum f s (x : xs) = (y : ys, s'')
 where
  (y , s' ) = f s x
  (ys, s'') = mapAccum f s' xs


zipBindsWith :: (a -> Variable -> Expr -> Bind) -> [a] -> Binds -> Binds
zipBindsWith f (x : _) (Strict (Bind var rhs)) = Strict (f x var rhs)
zipBindsWith f (x : _) (NonRec (Bind var rhs)) = NonRec (f x var rhs)
zipBindsWith f xs (Rec recs) =
  Rec (zipWith (\x (Bind var rhs) -> f x var rhs) xs recs)
zipBindsWith _ _ _ = error "zipBindsWith"

----------------------------------------------------------------
-- Alternatives functions
----------------------------------------------------------------

mapAlts :: (Pat -> Expr -> Alt) -> Alts -> Alts
mapAlts f = map (\(Alt pat expr) -> f pat expr)

zipAltsWith :: (a -> Pat -> Expr -> Alt) -> [a] -> Alts -> Alts
zipAltsWith f = zipWith (\x (Alt pat expr) -> f x pat expr)

----------------------------------------------------------------
--
----------------------------------------------------------------

mapExprWithSupply
  :: (NameSupply -> Expr -> Expr) -> NameSupply -> CoreModule -> CoreModule
mapExprWithSupply f supply m = m
  { moduleDecls = mapWithSupply fvalue supply (moduleDecls m)
  }
 where
  fvalue sup decl@DeclValue{} = decl { valueValue = f sup (valueValue decl) }
  fvalue _   decl             = decl


createFunction :: [Quantor] -> [Variable] -> Expr -> Type -> (Expr, Type)
createFunction quantors arguments bodyExpr bodyType =
  ( foldr (`Forall` KStar)  functionExpr quantors
  , foldr (`TForall` KStar) functionType quantors
  )
 where
  functionExpr = foldr (Lam False) bodyExpr arguments
  functionType = typeFunction (map variableType arguments) bodyType
