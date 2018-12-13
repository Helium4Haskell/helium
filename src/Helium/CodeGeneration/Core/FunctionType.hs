{-| Module      :  FunctionType
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Finds the function types of all toplevel functions

module Helium.CodeGeneration.Core.FunctionType (functionsList, functionsMap) where

import Data.Maybe (mapMaybe)
import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap(IdMap, mapFromList)
import Lvm.Common.Byte(stringFromBytes)
import Lvm.Core.Expr
import Lvm.Core.Module

import Helium.CodeGeneration.Iridium.Type

functionsList :: CoreModule -> [(Id, FunctionType)]
functionsList (Module _ _ _ decls) = mapMaybe functionInDecl decls

functionsMap :: CoreModule -> IdMap FunctionType
functionsMap = mapFromList . functionsList

functionInDecl :: CoreDecl -> Maybe (Id, FunctionType)
functionInDecl (DeclValue name _ _ expr _) = Just (name, FunctionType (replicate (arityOfExpr expr 0) TypeAny) TypeAnyWHNF)
functionInDecl decl = Nothing

arityOfExpr :: Expr -> Int -> Int
arityOfExpr (Lam _ expr) accum = arityOfExpr expr $ accum + 1
arityOfExpr _ accum = accum
