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
import Lvm.Common.Id    
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Utils

----------------------------------------------------------------
-- Environment: a name supply and a map from id to its arity
----------------------------------------------------------------
data Env    = Env NameSupply (IdMap Int)

uniqueId :: Env -> (Id, Env)
uniqueId (Env supply arities)
  = let (x,supply') = freshId supply
    in  (x,Env supply' arities)

findArity :: Id -> Env -> Int
findArity x (Env _ arities)
  = fromMaybe 0 (lookupMap x arities)

splitEnv :: Env -> (Env, Env)
splitEnv (Env supply arities)
  = let (s0,s1) = splitNameSupply supply
    in  (Env s0 arities, Env s1 arities)

splitEnvs :: Env -> [Env]
splitEnvs (Env supply arities)
  = map (`Env` arities) (splitNameSupplies supply)

----------------------------------------------------------------
-- coreSaturate
----------------------------------------------------------------
coreSaturate :: NameSupply -> CoreModule -> CoreModule
coreSaturate supply m
  = mapExprWithSupply (satDeclExpr arities) supply m
  where
    arities = mapFromList [(declName d,declArity d) | d <- moduleDecls m, isDeclCon d || isDeclExtern d]


satDeclExpr :: IdMap Int -> NameSupply -> Expr -> Expr
satDeclExpr arities supply = satExpr (Env supply arities)

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
      Lam var e
        -> Lam var (satExpr env e)
      _
        -> let expr'  = satExprSimple env expr
           in addLam env  (requiredArgs env expr') expr'

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
      Lam _ _     -> satExpr env expr
      Ap e1 e2    -> let (env1,env2) = splitEnv env
                     in  Ap (satExprSimple env1 e1) (satExpr env2 e2)
      _           -> expr

----------------------------------------------------------------
-- Add lambda's
----------------------------------------------------------------

addLam :: (Num a, Enum a) => Env -> a -> Expr -> Expr
addLam env n expr
  = let (_,ids) = mapAccumR (\env2 _ -> let (x,env') = uniqueId env2 in (env',x)) env [1..n]
    in  foldr (\x e -> Lam (Variable x TAny) e) (foldl Ap expr (map Var ids)) ids

requiredArgs :: Env -> Expr -> Int
requiredArgs env expr
  = case expr of
      Let _ _               -> 0
      Match _ _             -> 0
      Lam _ _               -> 0
      Ap e1 _               -> requiredArgs env e1 - 1
      Var x                 -> findArity x env
      Con (ConId x)         -> findArity x env
      Con (ConTag _ arity)  -> arity
      _                     -> 0
