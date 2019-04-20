{-| Module      :  Lift
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Lift lambdas and non-strict let declarations to toplevel.
-- Transforms the program such that all non-strict let declarations have a function application as binding.
-- We do so by adding new toplevel functions for those let declarations.
-- Furthermore we apply lambda lifting; all lambda expressions will be moved to toplevel declarations.
--
-- Before:
-- foo z =
--   let x = (let! y = f z in f y)
--   in f x
-- After:
-- ''x.1'' z = let! y = f z in f y
-- foo z = let x = ''x.1'' z in f x
--
-- Assumes that the AST is normalized, ie. the Normalize pass should be executed before.

module Helium.CodeGeneration.Core.Lift (coreLift) where

import Lvm.Common.Id
import Lvm.Common.IdSet
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Utils
import Helium.CodeGeneration.Core.TypeEnvironment

import Data.Maybe (catMaybes)

data Env = Env TypeEnvironment (IdMap Id)

typeEnv :: Env -> TypeEnvironment
typeEnv (Env te _) = te

modifyTypeEnv :: (TypeEnvironment -> TypeEnvironment) -> Env -> Env
modifyTypeEnv f (Env te mapping) = Env (f te) mapping

insertSubstitution :: Id -> Id -> Env -> Env
insertSubstitution from to (Env typeEnv mapping) = Env typeEnv $ insertMap from to mapping

coreLift :: NameSupply -> CoreModule -> CoreModule
coreLift supply mod@(Module name major minor decls) = Module name major minor decls'
  where
    decls' = concat $ mapWithSupply (liftExprInDecl typeEnv) supply decls
    typeEnv = typeEnvForModule mod

boundVar :: Bind -> Variable
boundVar (Bind var _) = var

liftExprInDecl :: TypeEnvironment -> NameSupply -> CoreDecl -> ([CoreDecl])
liftExprInDecl typeEnv supply (DeclValue name access enc expr customs) = DeclValue name access enc expr' customs : decls
  where
    (expr', decls) = liftExprIgnoreLambdas supply [] expr $ Env typeEnv emptyMap
liftExprInDecl _ _ decl = [decl]

liftExprIgnoreLambdas :: NameSupply -> [Either Quantor Variable] -> Expr -> Env -> (Expr, [CoreDecl])
liftExprIgnoreLambdas supply scope (Lam strict x expr) env = (Lam strict x expr', decls)
  where
    (expr', decls) = liftExprIgnoreLambdas supply (Right (variableSetStrict strict x) : scope) expr env'
    env' = modifyTypeEnv (typeEnvAddVariable x) env
liftExprIgnoreLambdas supply scope (Forall x k expr) env = (Forall x k expr', decls)
  where
    -- We should also keep track of all type variables which are in scope
    (expr', decls) = liftExprIgnoreLambdas supply (Left x : scope) expr env
liftExprIgnoreLambdas supply scope expr env = liftExpr supply scope expr env

liftExpr :: NameSupply -> [Either Quantor Variable] -> Expr -> Env -> (Expr, [CoreDecl])
liftExpr supply scope (Let (Strict b) e) env =
  ( case b' of
    Nothing -> e'
    Just bind -> Let (Strict bind) e'
  , decls1 ++ decls2
  )
  where
    (supply1, supply2) = splitNameSupply supply
    (b', decls1, envMap) = strictBind supply1 scope b env
    scope' = case b' of
      Nothing -> scope
      Just _ -> Right (variableSetStrict True $ boundVar b) : scope
    (e', decls2) = liftExpr supply2 (scope') e (envMap env')
    env' = modifyTypeEnv (typeEnvAddBind b) env
liftExpr supply scope (Let (NonRec b) e) env =
  ( case b' of
      Nothing -> e'
      Just bind -> Let (NonRec bind) e'
  , decls1 ++ decls2
  )
  where
    (supply1, supply2) = splitNameSupply supply
    (b', decls1, envMap) = lazyBind False supply1 scope b env
    scope' = case b' of
      Nothing -> scope
      Just _ -> Right (boundVar b) : scope
    (e', decls2) = liftExpr supply2 scope' e (envMap env')
    env' = modifyTypeEnv (typeEnvAddBind b) env
liftExpr supply scope (Let binds@(Rec bs) e) env = (Let (Rec $ catMaybes bs') e', concat decls1 ++ decls2)
  where
    scope' = map (Right . boundVar) bs ++ scope
    (supply1, supply2) = splitNameSupply supply
    (bs', decls1, envMaps) = unzip3 $ mapWithSupply (\s b -> lazyBind True s scope' b env) supply1 bs
    (e', decls2) = liftExpr supply2 scope' e (foldr id env' envMaps)
    env' = modifyTypeEnv (typeEnvAddBinds binds) env
liftExpr supply scope (Match name alts) env = (Match (rename env name) alts', concat decls)
  where
    (alts', decls) = unzip $ mapWithSupply (\s a -> liftAlt s scope a env) supply alts
-- Convert `\x -> expr` to `let y = \x -> expr in y
liftExpr supply scope expr@(Lam _ _ _) env = liftExpr supply' scope (Let (NonRec bind) (Var name)) env
  where
    (name, supply') = freshId supply
    bind = Bind (Variable name $ typeOfCoreExpression (typeEnv env) expr) expr
liftExpr supply scope (Forall x k expr) env = (Forall x k expr', decls)
  where
    (expr', decls) = liftExpr supply scope expr env
liftExpr supply scope (ApType expr t) env = (ApType expr' t, decls)
  where
    (expr', decls) = liftExpr supply scope expr env
-- After normalization the other expression constructors cannot have let bindings
-- as subexpressions, so we do not have to lift here. We do need to rename variables used in `expr`,
-- if they are mapped in `env`.
liftExpr supply scope expr env = (renameInSimpleExpr env expr, [])

-- Renames according to Env. Works on expressions consisting of Ap, Var, Con and Lit nodes.
renameInSimpleExpr :: Env -> Expr -> Expr
renameInSimpleExpr env (Var name) = Var $ rename env name
renameInSimpleExpr env (Ap e1 e2) = Ap (renameInSimpleExpr env e1) (renameInSimpleExpr env e2)
renameInSimpleExpr env (ApType e t) = ApType (renameInSimpleExpr env e) t
renameInSimpleExpr env e@(Con _) = e
renameInSimpleExpr env e@(Lit _) = e

rename :: Env -> Id -> Id
rename env@(Env _ mapping) name = case lookupMap name mapping of
  Nothing -> name
  Just name' -> rename env name'

isQuantifiedLambda :: Expr -> Bool
isQuantifiedLambda (Forall _ _ expr) = isQuantifiedLambda expr
isQuantifiedLambda (Lam _ _ _) = True
isQuantifiedLambda _ = False

strictBind :: NameSupply -> [Either Quantor Variable] -> Bind -> Env -> (Maybe Bind, [CoreDecl], Env -> Env)
strictBind supply scope b@(Bind _ expr) env
  | isQuantifiedLambda expr = lazyBind False supply scope b env
strictBind supply scope (Bind var expr) env = (Just $ Bind var expr', decls, id)
  where
    (expr', decls) = liftExpr supply scope expr env

lazyBind :: Bool -> NameSupply -> [Either Quantor Variable] -> Bind -> Env -> (Maybe Bind, [CoreDecl], Env -> Env)
lazyBind isRec supply scope b@(Bind var@(Variable x t) expr) env
  -- Expression can already be put in a thunk, don't need to change anything.
  | isValidThunk expr = (Just (Bind var $ renameInSimpleExpr env expr), [], id)
  -- Do not construct a Bind if the value is placed in a toplevel value which is not a Lambda
  | null scope = (Nothing, decl : decls, insertSubstitution x name)
  | otherwise = (Just $ Bind var ap, decl : decls, id)
  where
    ap = foldr addAp (Var name) scope
      where
        addAp (Left (Quantor idx _)) e = ApType e $ TVar idx
        addAp (Right (Variable name _)) e = Ap e $ Var name
    (name, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'

    argNames :: [(Either Quantor Variable, Either Quantor Variable)]
    argNames = mapWithSupply renameArg supply1 scope
      where
        renameArg s (Right var@(Variable arg t)) = (Right $ Variable arg t, Right $ Variable arg' t)
          where
            (arg', _) = freshIdFromId arg s
        renameArg s q = (q, q)

    env' = foldr (\(Variable arg _, Variable arg' _) -> insertSubstitution arg arg') env
      [(v1, v2) | (Right v1, Right v2) <- argNames]
    (expr', decls) = liftExprIgnoreLambdas supply2 (map snd argNames) expr env'
    value = foldl addArg expr' argNames
      where
        addArg e (_, Left quantor) = Forall quantor KStar e
        addArg e (_, Right (Variable name tp)) = Lam (typeIsStrict tp) (Variable name $ typeNotStrict tp) e
    decl :: CoreDecl
    decl = DeclValue
      { declName = name
      , declAccess = Defined False
      , declType = functionType (reverse scope)
      , valueValue = value
      , declCustoms = []
      }
    functionType :: [Either Quantor Variable] -> Type
    functionType [] = t
    functionType (Left quantor : args) = TForall quantor KStar $ functionType args
    functionType (Right (Variable name tArg) : args) = TAp (TAp (TCon TConFun) $ typeNotStrict tArg) $ functionType args

liftAlt :: NameSupply -> [Either Quantor Variable] -> Alt -> Env -> (Alt, [CoreDecl])
liftAlt supply scope (Alt pat expr) env = (Alt pat expr', decls)
  where
    (expr', decls) = liftExpr supply (map Right newVars ++ scope) expr env'
    env' = modifyTypeEnv (typeEnvAddVariables newVars) env
    newVars = patternVariables (typeEnv env) pat

isValidThunk :: Expr -> Bool
isValidThunk (Ap _ _) = True
isValidThunk (Forall _ _ e) = isValidThunk e
isValidThunk (ApType e _) = isValidThunk e
isValidThunk _ = False

variableSetStrict :: Bool -> Variable -> Variable
variableSetStrict strict (Variable name tp) = Variable name $ typeSetStrict strict tp
