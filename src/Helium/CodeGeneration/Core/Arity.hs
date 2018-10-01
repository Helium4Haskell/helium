{-| Module      :  Arity
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Finds the arities of all toplevel functions

module Helium.CodeGeneration.Core.Arity (aritiesList, aritiesMap) where

import Data.Maybe (mapMaybe)
import Lvm.Common.Id(Id)
import Lvm.Common.IdMap(IdMap, mapFromList)
import Lvm.Core.Expr
import Lvm.Core.Module

aritiesList :: CoreModule -> [(Id, Arity)]
aritiesList (Module _ _ _ decls) = mapMaybe arityInDecl decls

aritiesMap :: CoreModule -> IdMap Arity
aritiesMap = mapFromList . aritiesList

arityInDecl :: CoreDecl -> Maybe (Id, Int)
arityInDecl (DeclValue name _ _ expr _) = Just (name, arityOfExpr expr 0)
arityInDecl decl = Nothing

arityOfExpr :: Expr -> Int -> Int
arityOfExpr (Lam _ expr) accum = arityOfExpr expr $ accum + 1
arityOfExpr _ accum = accum
