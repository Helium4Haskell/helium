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

import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.Lvm.Core.Utils
import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Core.ReduceThunks (isCheap)

import Data.Maybe (catMaybes, maybeToList)
import Data.Either (lefts)
import Data.List (unzip4)

data Env = Env TypeEnvironment (IdMap Id)
type Scope = [Either Quantor Variable]

typeEnv :: Env -> TypeEnvironment
typeEnv (Env te _) = te

modifyTypeEnv :: (TypeEnvironment -> TypeEnvironment) -> Env -> Env
modifyTypeEnv f (Env te mapping) = Env (f te) mapping

insertSubstitution :: Id -> Id -> Env -> Env
insertSubstitution from to (Env typeEnv mapping) = Env typeEnv $ insertMap from to mapping

coreLift :: NameSupply -> CoreModule -> CoreModule
coreLift supply mod@(Module name major minor imports decls) = Module name major minor imports decls'
  where
    decls' = concat $ mapWithSupply (liftExprInDecl typeEnv) supply decls
    typeEnv = typeEnvForModule mod

boundVar :: Bind -> Variable
boundVar (Bind var _) = var

liftExprInDecl :: TypeEnvironment -> NameSupply -> CoreDecl -> ([CoreDecl])
liftExprInDecl typeEnv supply (DeclValue name access mod enc expr customs) = DeclValue name access mod enc expr' customs : decls
  where
    (expr', decls) = liftExprIgnoreLambdas supply [] expr $ Env typeEnv emptyMap
liftExprInDecl _ _ decl = [decl]

liftExprIgnoreLambdas :: NameSupply -> Scope -> Expr -> Env -> (Expr, [CoreDecl])
liftExprIgnoreLambdas supply scope (Lam strict x expr) env = (Lam strict x expr', decls)
  where
    (expr', decls) = liftExprIgnoreLambdas supply (Right (variableSetStrict strict x) : scope) expr env'
    env' = modifyTypeEnv (typeEnvAddVariable x) env
liftExprIgnoreLambdas supply scope (Forall x k expr) env = (Forall x k expr', decls)
  where
    -- We should also keep track of all type variables which are in scope
    (expr', decls) = liftExprIgnoreLambdas supply (Left x : scope) expr env
liftExprIgnoreLambdas supply scope expr env = liftExpr supply scope expr env

addBinds :: [Binds] -> Expr -> Expr
addBinds = flip $ foldr Let

liftBindss :: NameSupply -> Scope -> [Binds] -> Env -> ([Binds], [CoreDecl], Env)
liftBindss _ _ [] env = ([], [], env)
liftBindss supply scope (b:bs) env = (b' ++ bs', decls1 ++ decls2, env')
  where
    (supply1, supply2) = splitNameSupply supply
    (b', decls1, envMap, scope') = liftBinds supply1 scope b env
    (bs', decls2, env') = liftBindss supply2 scope' bs $ envMap env

liftBinds :: NameSupply -> Scope -> Binds -> Env -> ([Binds], [CoreDecl], Env -> Env, Scope)
liftBinds supply scope (Strict b) env = (map Strict (maybeToList b'), decls, envMap, scope')
  where
    (b', decls, envMap) = strictBind supply scope b env
    scope' = case b' of
      Nothing -> scope
      Just _ -> Right (variableSetStrict True $ boundVar b) : scope
liftBinds supply scope (NonRec b) env = (rotatedBinds ++ map NonRec (maybeToList b'), decls, envMap, scope')
  where
    (rotatedBinds, b', decls, envMap) = lazyBind False supply scope b env
    scope' = case b' of
      Nothing -> scope
      Just _ -> Right (boundVar b) : scope
liftBinds supply scope (Rec bs) env = (concat rotatedBindss ++ [Rec $ catMaybes bs'], concat declss, \env' -> foldr id env' envMaps, scope')
  where
    env1 = modifyTypeEnv (typeEnvAddBinds $ Rec bs) env
    scope' = map (Right . boundVar) bs ++ scope
    (rotatedBindss, bs', declss, envMaps) = unzip4 $ mapWithSupply (\s b -> lazyBind True s scope' b env1) supply bs

liftExpr :: NameSupply -> Scope -> Expr -> Env -> (Expr, [CoreDecl])
liftExpr supply scope (Let bs e) env = (addBinds bss e', decls1 ++ decls2)
  where
    (supply1, supply2) = splitNameSupply supply
    (bss, decls1, envMap, scope') = liftBinds supply1 scope bs env
    (e', decls2) = liftExpr supply2 scope' e (envMap $ Env (typeEnvAddBinds bs tenv) subst)
    Env tenv subst = env
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

strictBind :: NameSupply -> Scope -> Bind -> Env -> (Maybe Bind, [CoreDecl], Env -> Env)
strictBind supply scope b@(Bind _ expr) env
  | isQuantifiedLambda expr = case lazyBind False supply scope b env of
    ([], b', decls, f) -> (b', decls, f)
    _ -> error "strictBind: Expected zero additional binds"
strictBind supply scope (Bind var expr) env = (Just $ Bind var expr', decls, id)
  where
    (expr', decls) = liftExpr supply scope expr env

lazyBind :: Bool -> NameSupply -> Scope -> Bind -> Env -> ([Binds], Maybe Bind, [CoreDecl], Env -> Env)
lazyBind isRec supply scope b@(Bind var@(Variable x t) expr) env = case extractThunks expr of
  -- Expression can already be put in a thunk, don't need to change anything.
  Just (binds, expr') ->
    let
      (binds', decls', env') = liftBindss supply scope binds env
    in
      (binds', Just $ Bind var $ renameInSimpleExpr env' expr', decls', id)
  Nothing
    -- Do not construct a Bind if the value is placed in a toplevel value which is not a Lambda
    | null scope -> ([], Nothing, decl : decls, insertSubstitution x name)
    | otherwise  -> ([], Just $ Bind var ap, decl : decls, id)
  where
    ap = fst $ foldr addAp (Var name, length (lefts scope) - 1) scope
      where
        addAp (Left _) (e, nextTypeVar) = (ApType e $ TVar nextTypeVar, nextTypeVar - 1)
        addAp (Right (Variable name _)) (e, nextTypeVar) = (Ap e $ Var name, nextTypeVar)
    (name, supply') = freshId supply
    (supply1, supply2) = splitNameSupply supply'

    argNames :: [(Either Quantor Variable, Either Quantor Variable)]
    argNames = mapWithSupply renameArg supply1 scope
      where
        renameArg s (Right var@(Variable arg t)) = (Right $ Variable arg t, Right $ Variable arg' t)
          where
            (arg', _) = freshIdFromId arg s
        renameArg s q = (q, q)

    envDecl = foldr (\(Variable arg _, Variable arg' _) -> insertSubstitution arg arg') env
      [(v1, v2) | (Right v1, Right v2) <- argNames]
    (expr', decls) = liftExprIgnoreLambdas supply2 (map snd argNames) expr envDecl
    value = foldl addArg expr' argNames
      where
        addArg e (_, Left quantor) = Forall quantor KStar e
        addArg e (_, Right (Variable name tp)) = Lam (typeIsStrict tp) (Variable name $ typeNotStrict tp) e
    decl :: CoreDecl
    decl = DeclValue
      { declName = name
      , declAccess = Private
      , declModule = Nothing
      , declType = functionType (reverse scope)
      , valueValue = value
      , declCustoms = []
      }
    functionType :: Scope -> Type
    functionType [] = t
    functionType (Left quantor : args) = TForall quantor KStar $ functionType args
    functionType (Right (Variable name tArg) : args) = TAp (TAp (TCon TConFun) $ typeNotStrict tArg) $ functionType args

liftAlt :: NameSupply -> Scope -> Alt -> Env -> (Alt, [CoreDecl])
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

-- Tries to extract an expression which can be put in a thunk, by rotating (hosting) any binds that we encounter
extractThunks :: Expr -> Maybe ([Binds], Expr)
extractThunks = go 10
  where
    go :: Int -> Expr -> Maybe ([Binds], Expr)
    go budget expr
      | budget < 0 = Nothing -- Don't rotate too many binds, as that will cause that we consume a lot more memory
      | isValidThunk expr = Just ([], expr)
    go _ (Let b@(Strict (Bind _ bnd)) _)
      -- Don't rotate a strict bind, as this will cause that we evaluate things which we shouldn't
      -- However, if the bind is cheap then this won't matter.
      | not $ isCheap bnd = Nothing
    go budget (Let b expr) = case go (budget - length (listFromBinds b)) expr of
      Nothing -> Nothing
      Just (binds, expr') -> Just (b : binds, expr')
    go _ _ = Nothing

variableSetStrict :: Bool -> Variable -> Variable
variableSetStrict strict (Variable name tp) = Variable name $ typeSetStrict strict tp
