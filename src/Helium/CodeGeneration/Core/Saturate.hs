--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

----------------------------------------------------------------
-- saturate all calls to externals, instructions and constructors.
-- pre: [coreNoShadow]
----------------------------------------------------------------

-- Note: We only use this for saturating constructors. We could remove the functionality for externals.
module Helium.CodeGeneration.Core.Saturate (coreSaturate) where

import Data.List
import Data.Maybe
import Helium.Lvm.Common.Id    
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.Utils
import Helium.CodeGeneration.Core.TypeEnvironment

----------------------------------------------------------------
-- Environment: a name supply and a map from id to the function
-- type, containing its required arguments
----------------------------------------------------------------
data Env    = Env NameSupply (IdMap Type)

uniqueId :: Env -> (Id, Env)
uniqueId (Env supply requiredArgs)
  = let (x,supply') = freshId supply
    in  (x,Env supply' requiredArgs)

findConstructorType :: Id -> Env -> Maybe Type
findConstructorType x (Env _ requiredArgs)
  = lookupMap x requiredArgs

splitEnv :: Env -> (Env, Env)
splitEnv (Env supply requiredArgs)
  = let (s0,s1) = splitNameSupply supply
    in  (Env s0 requiredArgs, Env s1 requiredArgs)

splitEnvs :: Env -> [Env]
splitEnvs (Env supply requiredArgs)
  = map (`Env` requiredArgs) (splitNameSupplies supply)

----------------------------------------------------------------
-- coreSaturate
----------------------------------------------------------------
coreSaturate :: NameSupply -> CoreModule -> CoreModule
coreSaturate supply m
  = mapExprWithSupply (satDeclExpr constructors) supply m
  where
    constructors = mapFromList [(declName d, declType d) | d <- moduleDecls m, isDeclCon d || isDeclExtern d]

extractArguments :: Type -> [Type]
extractArguments (TForall _ _ t) = extractArguments t
extractArguments (TAp (TAp (TCon TConFun) t1) t2) = t1 : extractArguments t2
extractArguments _ = []

satDeclExpr :: IdMap Type -> NameSupply -> Expr -> Expr
satDeclExpr requiredArgs supply = satExpr (Env supply requiredArgs)

----------------------------------------------------------------
-- saturate expressions
----------------------------------------------------------------
satExpr :: Env -> Expr -> Expr
satExpr env expr
  = case expr of
      Let binds e
        -> let (env0,env1) = splitEnv env
           in  Let (satBinds env0 binds) (satExpr env1 e)
      Match x alts
        -> Match x (satAlts env alts)
      Lam strict var e
        -> Lam strict var (satExpr env e)
      Forall x k e
        -> Forall x k $ satExpr env e
      _
        ->
          let expr'  = satExprSimple env expr
          in
            case requiredArgs env expr' of
              Nothing -> expr'
              Just tp -> addLam env (extractArguments tp) expr'

satBinds :: Env -> Binds -> Binds
satBinds = zipBindsWith (\env var expr -> Bind var (satExpr env expr)) . splitEnvs

satAlts :: Env -> Alts -> Alts
satAlts = zipAltsWith (\env pat expr -> Alt pat (satExpr env expr)) . splitEnvs

-- don't saturate Ap, Var and Con here
satExprSimple :: Env -> Expr -> Expr
satExprSimple env expr
  = case expr of
      Let _ _     -> satExpr env expr
      Match _ _   -> satExpr env expr
      Lam _ _ _   -> satExpr env expr
      Forall _ _ _ -> satExpr env expr
      ApType e t  -> ApType (satExprSimple env e) t
      Ap e1 e2    -> let (env1,env2) = splitEnv env
                     in  Ap (satExprSimple env1 e1) (satExpr env2 e2)
      _           -> expr

----------------------------------------------------------------
-- Add lambda's
----------------------------------------------------------------

addLam :: Env -> [Type] -> Expr -> Expr
addLam env args expr
  = let (_, vars) = mapAccumR (\env2 t -> let (x,env') = uniqueId env2 in (env', Variable x t)) env args
    in  foldr (Lam False) (foldl Ap expr (map (Var . variableName) vars)) vars

-- Returns the function type containing the remaining required types
requiredArgs :: Env -> Expr -> Maybe Type
requiredArgs env expr
  = case expr of
      Ap e1 _               -> case requiredArgs env e1 of
        Just (TAp (TAp (TCon TConFun) _) t) -> Just t
        Nothing -> Nothing
      ApType e1 t2 -> case requiredArgs env e1 of
        Just t1 -> Just $ typeApply t1 t2
        Nothing -> Nothing
      Con (ConId x)         -> findConstructorType x env
      Con (ConTuple arity)  -> Just $ typeTuple arity
      _                     -> Nothing
