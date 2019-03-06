--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

----------------------------------------------------------------
-- Make all declarations (in lets, lambdas and match expressions)
-- globally unique.
----------------------------------------------------------------
module Helium.CodeGeneration.Core.Rename (coreRename) where

import Data.Maybe
import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet 
import Lvm.Core.Expr
import Lvm.Core.Utils

----------------------------------------------------------------
-- Environment: name supply, id's in scope & renamed identifiers
----------------------------------------------------------------
data Env  = Env NameSupply IdSet (IdMap Id)

renameBinders :: Env -> [Id] -> (Env, [Id])
renameBinders env bs
  = let (env',bs') = foldl (\(env1,ids) x1 -> renameBinder env1 x1 $ \env2 x2 -> (env2,x2:ids)) (env,[]) bs
    in  (env',reverse bs')

renameLetBinder :: Env -> Id -> (Env -> Id -> a) -> a
renameLetBinder (Env supply inscope renaming) x cont
    = let (x2,supply') = freshIdFromId x supply
          inscope'      = insertSet x inscope
          renaming'     = extendMap x x2 renaming
      in cont (Env supply' inscope' renaming') x2

renameBinder :: Env -> Id -> (Env -> Id -> a) -> a
renameBinder env@(Env supply set m) x cont
  | elemSet x set
      = renameLetBinder env x cont
  | otherwise
      = cont (Env supply (insertSet x set) m) x

renameVar :: Env -> Id -> Id
renameVar (Env _ _ m) x
  = fromMaybe x (lookupMap x m)

splitEnv :: Env -> (Env,Env)
splitEnv (Env supply set m)
  = let (s0,s1) = splitNameSupply supply
    in  (Env s0 set m,Env s1 set m)

splitEnvs :: Env -> [Env]
splitEnvs (Env supply set idmap)
  = map (\s -> Env s set idmap) (splitNameSupplies supply)

coreRename :: NameSupply -> CoreModule -> CoreModule
coreRename supply m = mapExprWithSupply (nsDeclExpr (runAnalysis m `unionSet` globalNames m)) supply m

nsDeclExpr :: IdSet -> NameSupply -> Expr -> Expr
nsDeclExpr inscope supply = nsExpr (Env supply inscope emptyMap)


nsExpr :: Env -> Expr -> Expr
nsExpr env expr
  = case expr of
      Let binds e       -> nsBinds env binds $ \env' binds' ->
                           Let binds' (nsExpr env' e)
      Match x alts      -> Match (renameVar env x) (nsAlts env alts)
      Lam (Variable x t) e -> renameBinder env x $ \env2 x2 ->
                           Lam (Variable x2 t) (nsExpr env2 e)
      Ap expr1 expr2    -> let (env1,env2) = splitEnv env
                           in  Ap (nsExpr env1 expr1) (nsExpr env2 expr2)
      Var x             -> Var (renameVar env x)
      Con (ConTag e a)  -> Con (ConTag (nsExpr env e) a)
      Forall x k e      -> Forall x k $ nsExpr env e
      _                 -> expr

nsBinds :: Env -> Binds -> (Env -> Binds -> a) -> a
nsBinds env binds cont
  = case binds of
      Strict (Bind var rhs)  -> nonrec Strict var rhs
      NonRec (Bind var rhs)  -> nonrec NonRec var rhs
      Rec _                -> rec_
  where
    nonrec make (Variable x1 t1) rhs
      = renameLetBinder env x1 $ \env' x2 ->
        cont env' (make (Bind (Variable x2 t1) (nsExpr env rhs)))
      
    rec_ 
      = let (binds',env') = mapAccumBinds (\env1 (Variable x1 t1) rhs -> renameLetBinder env1 x1 $ \env2 x2 -> (Bind (Variable x2 t1) rhs,env2))
                                           env binds
        in cont env' (zipBindsWith (\env1 (Variable x1 t1) rhs -> Bind (Variable x1 t1) (nsExpr env1 rhs)) (splitEnvs env') binds')

nsAlts :: Env -> Alts -> Alts
nsAlts = zipAltsWith nsAlt . splitEnvs

nsAlt :: Env -> Pat -> Expr -> Alt
nsAlt env pat expr
  = let (pat',env') = nsPat env pat
    in Alt pat' (nsExpr env' expr)

nsPat :: Env -> Pat -> (Pat, Env)
nsPat env pat
  = case pat of
      PatCon con ids -> let (env',ids') = renameBinders env ids
                        in (PatCon con ids',env')
      other          -> (other,env)

-- Analysis to find identifiers that have multiple definitions.
-- If an identifier is not in the IdMap, it means that the identifier is not defined in the expression.
-- If the value if False, it is defined once. If the value is true, there are multiple definitions.

type Analysis = IdMap Bool

runAnalysis :: CoreModule -> IdSet
runAnalysis = setFromList . map fst . filter snd . listFromMap . analyse

analyse :: CoreModule -> Analysis
analyse (Module _ _ _ decls) = foldr analyseDecl emptyMap decls

analyseDecl :: CoreDecl -> Analysis -> Analysis
analyseDecl (DeclValue _ _ _ expr _) = dupUnion $ duplicateNames expr
analyseDecl _ = id

{-
data Expr       = Let       !Binds Expr       
                | Match     !Id Alts
                | Ap        Expr Expr
                | Lam       !Id Expr
                | Con       !(Con Expr)
                | Var       !Id
                | Lit       !Literal
                -}
duplicateNames :: Expr -> Analysis
duplicateNames (Let bs expr) = dupInserts (varsInBinds bs) $ duplicateNames expr
duplicateNames (Match _ alts) = foldr1 dupUnion $ map duplicateNamesInAlt alts
duplicateNames (Ap e1 e2) = dupUnion (duplicateNames e1) (duplicateNames e2)
duplicateNames (Lam (Variable x _) expr) = dupInsert x $ duplicateNames expr
duplicateNames _ = emptyMap -- Con, Var or Lit

duplicateNamesInAlt :: Alt -> Analysis
duplicateNamesInAlt (Alt (PatCon _ args) expr) = dupInserts args $ duplicateNames expr
duplicateNamesInAlt (Alt _ expr) = duplicateNames expr

dupUnion :: Analysis -> Analysis -> Analysis
dupUnion = unionMapWith (\_ _ -> True)

dupInsert :: Id -> Analysis -> Analysis
dupInsert name m = updateMap name (name `elemMap` m) m

dupInserts :: [Id] -> Analysis -> Analysis
dupInserts = flip $ foldr dupInsert

varsInBinds :: Binds -> [Id]
varsInBinds (Strict b) = return $ varInBind b
varsInBinds (NonRec b) = return $ varInBind b
varsInBinds (Rec bs) = map varInBind bs

varInBind :: Bind -> Id
varInBind (Bind (Variable x _) _) = x
