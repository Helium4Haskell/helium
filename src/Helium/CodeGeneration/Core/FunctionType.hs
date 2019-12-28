{-| Module      :  FunctionType
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Finds the function types of all toplevel functions

module Helium.CodeGeneration.Core.FunctionType (functionsMap) where

import Data.Maybe (mapMaybe)
import Lvm.Common.Id(Id, idFromString)
import Lvm.Common.IdMap(IdMap, mapFromList)
import Lvm.Common.Byte(stringFromBytes)
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Iridium.Type

functionsList :: TypeEnvironment -> CoreModule -> [(Id, (Type, FunctionType))]
functionsList env (Module _ _ _ _ decls) = mapMaybe (functionInDecl env) decls

functionsMap :: TypeEnvironment -> CoreModule -> IdMap (Type, FunctionType)
functionsMap env = mapFromList . functionsList env

functionInDecl :: TypeEnvironment -> CoreDecl -> Maybe (Id, (Type, FunctionType))
functionInDecl env (DeclValue name _ _ tp expr _) = Just (name, (tp', fnType))
  where
    arity = arityOfExpr expr 0
    tp' = updateFunctionTypeStrictness env (getExpressionStrictness expr) tp
    fnType = extractFunctionTypeWithArity env arity tp'
functionInDecl env decl = Nothing

arityOfExpr :: Expr -> Int -> Int
arityOfExpr (Forall _ _ expr) accum = arityOfExpr expr accum
arityOfExpr (Lam _ _ expr) accum = arityOfExpr expr $ accum + 1
arityOfExpr _ accum = accum
