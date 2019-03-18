{-| Module      :  TypeEnvironment
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- A type environment for type inference in Core files

module Helium.CodeGeneration.Core.TypeEnvironment where

import Data.Maybe

import Helium.Utils.Utils
import Lvm.Core.Module
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

data TypeEnvironment = TypeEnvironment
  { typeEnvSynonyms :: IdMap Type
  , typeEnvValues :: IdMap Type
  }

typeEnvForModule :: CoreModule -> TypeEnvironment
typeEnvForModule (Module _ _ _ decls) = TypeEnvironment (mapFromList synonyms) (mapFromList values)
  where
    synonyms = [ (name, tp) | DeclTypeSynonym name _ tp _ <- decls ]
    values = mapMaybe findValue decls
    findValue :: CoreDecl -> Maybe (Id, Type)
    findValue decl
      | isValue decl = Just (declName decl, declType decl)
      | otherwise = Nothing
    isValue :: CoreDecl -> Bool
    isValue DeclValue{} = True
    isValue DeclAbstract{} = True
    isValue DeclCon{} = True
    isValue _ = False

typeEnvAddVariable :: Variable -> TypeEnvironment -> TypeEnvironment
typeEnvAddVariable (Variable name tp) env = env{ typeEnvValues = updateMap name tp $ typeEnvValues env }

typeEnvAddVariables :: [Variable] -> TypeEnvironment -> TypeEnvironment
typeEnvAddVariables vars env = foldr typeEnvAddVariable env vars

typeEnvAddBind :: Bind -> TypeEnvironment -> TypeEnvironment
typeEnvAddBind (Bind var _) = typeEnvAddVariable var

typeEnvAddBinds :: Binds -> TypeEnvironment -> TypeEnvironment
typeEnvAddBinds (Strict bind) env = typeEnvAddBind bind env
typeEnvAddBinds (NonRec bind) env = typeEnvAddBind bind env
typeEnvAddBinds (Rec binds) env = foldr typeEnvAddBind env binds

typeEnvAddPattern :: Pat -> TypeEnvironment -> TypeEnvironment
typeEnvAddPattern (PatCon (ConTuple _) tps ids) env
  = typeEnvAddVariables (zipWith Variable ids tps) env
typeEnvAddPattern (PatCon (ConId name) tps ids) env
  = typeEnvAddVariables (findVars ids conType) env
  where
    conType = typeApplyList (typeOfId env name) tps
    findVars :: [Id] -> Type -> [Variable]
    findVars (x:xs) (TAp (TAp (TCon TConFun) tArg) tReturn)
      = Variable x tArg : findVars xs tReturn
    findVars [] _ = []
    findVars _ tp = internalError "Core.TypeEnvironment" "typeEnvAddPattern" $ "Expected function type for constructor " ++ show name ++ ", got " ++ show tp

typeNormalizeHead :: TypeEnvironment -> Type -> Type
typeNormalizeHead env = expand []
  where
    expand args (TStrict t) = expand args t
    expand args (TAp t1 t2) = expand (t2 : args) t1
    expand args tp@(TCon (TConDataType name)) = case lookupMap name $ typeEnvSynonyms env of
      Just tp' -> expand [] $ typeApplyList tp' args
      _ -> typeApplyList tp args
    expand args tp = typeApplyList tp args

typeOfId :: TypeEnvironment -> Id -> Type
typeOfId env name = case lookupMap name $ typeEnvValues env of
  Just tp -> tp
  Nothing -> internalError "Core.TypeEnvironment" "typeOfId" $ "variable " ++ show name ++ " not found in type environment"

typeOfCoreExpression :: TypeEnvironment -> Expr -> Type

-- Find type of the expression in the Let
typeOfCoreExpression env (Let binds expr)
  = typeOfCoreExpression (typeEnvAddBinds binds env) expr

-- All Alternatives of a Match should have the same return type,
-- so we only have to check the first one.
typeOfCoreExpression env (Match name (Alt pattern expr : _))
  = typeOfCoreExpression env' expr
  where
    env' = typeEnvAddPattern pattern env

-- Expression: e1 e2
-- Resolve the type of e1, which should be a function type.
typeOfCoreExpression env (Ap e1 e2) = case typeNormalizeHead env $ typeOfCoreExpression env e1 of
  TAp (TAp (TCon TConFun) _) tReturn -> tReturn
  tp -> internalError "Core.TypeEnvironment" "typeOfCoreExpression" $ "expected a function type in the first argument of a function application, got " ++ show tp

-- Expression: e1 { tp1 }
-- The type of e1 should be of the form `forall x. tp2`. Substitute x with tp1 in tp2.
typeOfCoreExpression env (ApType e1 tp1) = case typeNormalizeHead env $ typeOfCoreExpression env e1 of
  TForall (Quantor idx _) _ tp2 -> typeSubstitute idx tp1 tp2
  tp -> internalError "Core.TypeEnvironment" "typeOfCoreExpression" $ "typeOfCoreExpression: expected a forall type in the first argument of a function application, got " ++ show tp

-- Expression: \x: t1 -> e
-- If e has type t2, then the lambda has type t1 -> t2
typeOfCoreExpression env (Lam var@(Variable _ tp) expr) =
  typeFunction [tp] $ typeOfCoreExpression env' expr
  where
    env' = typeEnvAddVariable var env

-- Expression: forall x. expr
-- If expr has type t, then the forall expression has type `forall x. t`.
typeOfCoreExpression env (Forall x kind expr) =
  TForall x kind $ typeOfCoreExpression env expr

-- Expression: (,)
-- Type: forall a. forall b. a -> b -> (a, b)
typeOfCoreExpression env (Con (ConTuple arity)) =
  foldr (\var -> TForall (Quantor var Nothing) KStar) tp vars
  where
    -- Type without quantifications, eg (a, b)
    tp = foldl (\t var -> TAp t $ TVar var) (TCon $ TConTuple arity) vars
    vars = [0 .. arity - 1]

-- Resolve the type of a variable or constructor
typeOfCoreExpression env (Con (ConId x)) = typeOfId env x
typeOfCoreExpression env (Var x) = typeOfId env x

-- Types of literals
typeOfCoreExpression _ (Lit lit) = typeOfLiteral lit

-- Checks type equivalence
typeEqual :: TypeEnvironment -> Type -> Type -> Bool
typeEqual env TAny TAny = True
typeEqual env (TStrict t1) t2 = typeEqual env t1 t2 -- Ignore strictness
typeEqual env t1 (TStrict t2) = typeEqual env t1 t2 -- Ignore strictness
typeEqual env (TVar x1) (TVar x2) = x1 == x2
typeEqual env (TCon c1) (TCon c2) = c1 == c2
typeEqual env t1@(TAp _ _) t2 = typeEqualNoTypeSynonym env (typeNormalizeHead env t1) (typeNormalizeHead env t2)
typeEqual env t1 t2@(TAp _ _) = typeEqualNoTypeSynonym env t1 (typeNormalizeHead env t2)
typeEqual env (TForall (Quantor x _) _ t1) (TForall (Quantor y _) _ t2) =
  typeEqual env t1 (typeSubstitute y (TVar x) t2)
typeEqual env _ _ = False

-- Checks type equivalence, assuming that there is no synonym at the head of the type
typeEqualNoTypeSynonym :: TypeEnvironment -> Type -> Type -> Bool
typeEqualNoTypeSynonym env (TAp tl1 tl2) (TAp tr1 tr2)
  = typeEqual env tl1 tr1
  && typeEqualNoTypeSynonym env tl2 tr2
typeEqualNoTypeSynonym _ (TAp _ _) _ = False
typeEqualNoTypeSynonym _ _ (TAp _ _) = False
typeEqualNoTypeSynonym env t1 t2 = typeEqual env t1 t2

typeOfLiteral :: Literal -> Type
typeOfLiteral (LitInt _) = TCon $ TConDataType $ idFromString "Int"
typeOfLiteral (LitDouble _) = TCon $ TConDataType $ idFromString "Double"
typeOfLiteral (LitBytes _) = TCon $ TConDataType $ idFromString "String"
