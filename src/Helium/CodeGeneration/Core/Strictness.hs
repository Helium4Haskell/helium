module Helium.CodeGeneration.Core.Strictness (coreStrictness) where

import Data.List
import Text.PrettyPrint.Leijen (pretty)

import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Common.IdSet
import Helium.Lvm.Core.Expr
import Helium.Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.Lvm.Core.Module

coreStrictness :: NameSupply -> CoreModule -> CoreModule
coreStrictness supply mod@(Module name major minor imports decls) = Module name major minor imports $ mapWithSupply (transformDeclaration env) supply decls
  where
    env = envForModule mod

data Env = Env
  { envTypeEnv :: !TypeEnvironment
  , envFunctionArguments :: !(IdMap [Bool])
  }

getAbstractStrictness :: TypeEnvironment -> Int -> Type -> [Bool]
getAbstractStrictness typeEnv arity tp = [ typeIsStrict tArg | Right tArg <- args ]
  where
    FunctionType args _ = extractFunctionTypeWithArity typeEnv arity tp

getConstructorStrictness :: Type -> [Bool]
getConstructorStrictness tp = [ typeIsStrict tArg | Right tArg <- args ]
  where
    FunctionType args _ = extractFunctionTypeNoSynonyms tp

envForModule :: CoreModule -> Env
envForModule mod@(Module _ _ _ _ decls) = Env typeEnv (mapFromList $ argsValues ++ argsAbstracts ++ argsConstructors)
  where
    typeEnv = typeEnvForModule mod
    argsValues = [ (name, getExpressionStrictness expr) | DeclValue name _ _ _ expr _ <- decls ]
    argsAbstracts = [ (name, getAbstractStrictness typeEnv arity tp) | DeclAbstract name _ _ arity tp _ <- decls ]
    argsConstructors = [ (name, getConstructorStrictness tp) | DeclCon name _ _ tp _ _ <- decls ]

data Analysis a = Analysis IdSet !a

transformDeclaration :: Env -> NameSupply -> CoreDecl -> CoreDecl
transformDeclaration env supply decl@DeclValue{} = decl{ valueValue = expr }
  where
    Analysis _ expr = analyseExpression env supply $ valueValue decl
transformDeclaration _ _ decl = decl

analyseExpression :: Env -> NameSupply -> Expr -> Analysis Expr
analyseExpression env supply (Let (Strict bind@(Bind (Variable name tp) _)) expr) = Analysis strict $ Let (Strict bind') expr'
  where
    (supply1, supply2) = splitNameSupply supply
    strict = strict1 `unionSet` (deleteSet name strict2)
    Analysis strict1 bind' = analyseBind env supply1 bind
    Analysis strict2 expr' = analyseExpression env supply2 expr
analyseExpression env supply (Let (NonRec bind@(Bind var@(Variable name _) _)) expr)
  -- Bind is strict. Create a strict bind and propagate the strictness information from the bind in `strict2`.
  | name `elemSet` strict1 = Analysis (unionSet strict strict2) $ Let (Strict bind'') expr'
  -- Bind is not strict. Do not propagate the derived strictness information from the bind in `strict2`.
  | otherwise = Analysis strict $ Let (NonRec bind') expr'
  where
    (supply1, supply2) = splitNameSupply supply
    strict = deleteSet name strict1
    Analysis strict1 expr' = analyseExpression env supply1 expr
    Analysis strict2 bind'@(Bind _ bindExpr) = analyseBind env supply2 bind
    bind'' = Bind var bindExpr
analyseExpression env supply (Let (Rec binds) expr) = Analysis (unionSet strictExpr strictBinds) $ Let (Rec binds') expr'
  where
    (supplyExpr, supplyBinds) = splitNameSupply supply
    Analysis strictExpr expr' = analyseExpression env supplyExpr expr
    Analysis strictBinds binds' = analyseRecBinds env strictExpr supplyBinds binds 
analyseExpression env supply (Match var alts) = Analysis (foldr1 intersectionSet stricts) $ Match var alts'
  where
    (stricts, alts') = unzip $ map (\(Analysis s a) -> (s, a)) $ mapWithSupply (analyseAlt env) supply alts
analyseExpression _ _ expr@(Lit _) = Analysis emptySet expr
analyseExpression env supply expr@(Lam _ _ _) = Analysis emptySet expr'
  where
    -- Do not propagate the strictness information from the function, as it may not be invoked
    Analysis _ expr' = analyseFunction env supply expr
analyseExpression env supply (Forall quantor kind expr) = Analysis strict $ Forall quantor kind expr'
  where
    Analysis strict expr' = analyseExpression env supply expr
analyseExpression env supply expr = Analysis strict expr
  where
    Analysis strict _ = analyseApplication env expr 0

analyseApplication :: Env -> Expr -> Int -> Analysis [Bool]
analyseApplication env (Ap expr (Var arg)) arity = Analysis strict' $ drop 1 argStrictness
  where
    Analysis strict argStrictness = analyseApplication env expr (arity + 1)
    strict' = case argStrictness of
      True : _ -> insertSet arg strict
      _ -> strict
analyseApplication env (ApType expr _) arity = analyseApplication env expr arity
analyseApplication env (Var name) arity = case lookupMap name $ envFunctionArguments env of
  Just args
    -- Saturated call
    | arity >= length args -> Analysis emptySet args
    -- Unsaturated call. We cannot derive any strictness information on the applied arguments,
    -- as we do not know whether the partially applied function will be called later on.
    | otherwise -> Analysis emptySet args
  _ -> Analysis (singleSet name) []
analyseApplication env (Con (ConId name)) arity = case lookupMap name $ envFunctionArguments env of
  Just args
    | arity >= length args -> Analysis emptySet args
  _ -> Analysis emptySet []
analyseApplication _ (Con _) _ = Analysis emptySet []
analyseApplication _ expr _ = error ("Strictness.analyseApplication: expected application, got " ++ show (pretty expr))

analyseFunction :: Env -> NameSupply -> Expr -> Analysis Expr
analyseFunction env supply (Lam s var@(Variable name _) expr) = Analysis strict $ Lam (s || name `elemSet` strict) var expr'
  where
    Analysis strict expr' = analyseFunction env supply expr
analyseFunction env supply (Forall quantor kind expr) = Analysis strict $ Forall quantor kind expr'
  where
    Analysis strict expr' = analyseFunction env supply expr
analyseFunction env supply expr = analyseExpression env supply expr

analyseBind :: Env -> NameSupply -> Bind -> Analysis Bind
analyseBind env supply (Bind var expr) = Analysis strict $ Bind var expr'
  where
    Analysis strict expr' = analyseExpression env supply expr

-- TODO: Remove declared variables from IdSet
analyseRecBinds :: Env -> IdSet -> NameSupply -> [Bind] -> Analysis [Bind]
analyseRecBinds env stricts supply binds = Analysis (unionSet strict1 strict2) (strictBinds' ++ lazyBinds')
  where
    (strictBinds, lazyBinds) = partition bindIsStrict binds
    bindIsStrict (Bind (Variable name _) _) = name `elemSet` stricts
    (supplyStrict, supplyLazy) = splitNameSupply supply
    Analysis strict1 strictBinds' = analyseStrictRecBinds env supplyStrict strictBinds
    Analysis strict2 lazyBinds'
      | null strictBinds = Analysis emptySet $ mapWithSupply (\s (Bind var expr) -> let Analysis _ expr' = analyseExpression env s expr in Bind var expr') supplyLazy lazyBinds
      -- Some more binds may become strict, after analysing `strictBinds`
      | otherwise = analyseRecBinds env stricts supplyLazy lazyBinds

analyseStrictRecBinds :: Env -> NameSupply -> [Bind] -> Analysis [Bind]
analyseStrictRecBinds env supply binds = foldr analyseStrictRecBind (Analysis emptySet []) $ zip (splitNameSupplies supply) binds
  where
    analyseStrictRecBind :: (NameSupply, Bind) -> Analysis [Bind] -> Analysis [Bind]
    analyseStrictRecBind (s, bind) (Analysis strict bs) = Analysis (unionSet strict strict') (bind' : bs)
      where
        Analysis strict' bind' = analyseBind env s bind 

-- TODO: Remove declared variables from IdSet
analyseAlt :: Env -> NameSupply -> Alt -> Analysis Alt
analyseAlt env supply (Alt pat expr) = Analysis strict $ Alt pat expr'
  where
    Analysis strict expr' = analyseExpression env supply expr
