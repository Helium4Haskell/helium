{-| Module      :  TypeEnvironment
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- A type environment for type inference in Core files

module Helium.CodeGeneration.Core.TypeEnvironment where

import Data.Maybe
import Data.Either (rights)

import Helium.Utils.Utils
import Lvm.Core.Module
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import Text.PrettyPrint.Leijen

data TypeEnvironment = TypeEnvironment
  { typeEnvSynonyms :: IdMap Type
  , typeEnvGlobalValues :: IdMap Type
  , typeEnvLocalValues  :: IdMap Type
  }

typeEnvForModule :: CoreModule -> TypeEnvironment
typeEnvForModule (Module _ _ _ _ decls) = TypeEnvironment (mapFromList synonyms) (mapFromList values) emptyMap
  where
    synonyms = [ (name, tp) | DeclTypeSynonym name _ _ _ tp _ <- decls ]
    values = mapMaybe findValue decls
    findValue :: CoreDecl -> Maybe (Id, Type)
    findValue decl
      | isValue decl = Just (declName decl, typeRemoveArgumentStrictness $ declType decl)
      | otherwise = Nothing
    isValue :: CoreDecl -> Bool
    isValue DeclValue{} = True
    isValue DeclAbstract{} = True
    isValue DeclCon{} = True
    isValue _ = False

typeEnvAddGlobalValue :: Id -> Type -> TypeEnvironment -> TypeEnvironment
typeEnvAddGlobalValue name tp env = env{ typeEnvGlobalValues = insertMap name tp $ typeEnvGlobalValues env }

typeEnvAddGlobalValues :: [(Id, Type)] -> TypeEnvironment -> TypeEnvironment
typeEnvAddGlobalValues = flip $ foldr (uncurry typeEnvAddGlobalValue)

typeEnvAddVariable :: Variable -> TypeEnvironment -> TypeEnvironment
typeEnvAddVariable (Variable name tp) env = env{ typeEnvLocalValues = updateMap name (normalizeType tp) $ typeEnvLocalValues env }
  where
    normalizeType = typeNotStrict . typeNotAnnotated

typeEnvAddVariables :: [Variable] -> TypeEnvironment -> TypeEnvironment
typeEnvAddVariables vars env = foldr typeEnvAddVariable env vars

typeEnvAddBind :: Bind -> TypeEnvironment -> TypeEnvironment
typeEnvAddBind (Bind var _) = typeEnvAddVariable var

typeEnvAddBinds :: Binds -> TypeEnvironment -> TypeEnvironment
typeEnvAddBinds (Strict bind) env = typeEnvAddBind bind env
typeEnvAddBinds (NonRec bind) env = typeEnvAddBind bind env
typeEnvAddBinds (Rec binds) env = foldr typeEnvAddBind env binds

typeEnvWeaken :: Int -> TypeEnvironment -> TypeEnvironment
typeEnvWeaken 0 env = env
typeEnvWeaken k env = env{ typeEnvLocalValues = fmap (typeWeaken k) $ typeEnvLocalValues env }

patternVariables :: TypeEnvironment -> Pat -> [Variable]
patternVariables _ (PatCon (ConTuple _) tps ids)
  = (zipWith Variable ids tps)
patternVariables env (PatCon (ConId name) tps ids)
  = findVars ids apType
  where
    conType = typeOfId env name
    (conType', tps') = annApplyList conType tps env
    apType = typeApplyList conType' tps'
    findVars :: [Id] -> Type -> [Variable]
    findVars (x:xs) (TAp (TAp (TCon TConFun) tArg) tReturn)
      = Variable x tArg : findVars xs tReturn
    findVars [] _ = []
    findVars _ tp = internalError "Core.TypeEnvironment" "patternVariables" $ "Expected function type for constructor " ++ show name ++ ", got " ++ showType [] tp
patternVariables _ _ = [] -- Literal or default

typeEnvAddPattern :: Pat -> TypeEnvironment -> TypeEnvironment
typeEnvAddPattern pat env
  = typeEnvAddVariables (patternVariables env pat) env

typeNormalizeHead :: TypeEnvironment -> Type -> Type
typeNormalizeHead env = normalize False
  where
    normalize strict (TAp t1 t2) = case normalize False t1 of
      t1'@(TForall _ _ _) -> normalize strict $ typeApply t1' t2
      t1' ->
        let tp = TAp t1' t2
        in if strict then TStrict tp else tp
    normalize _ (TStrict t1) = normalize True t1
    normalize strict t1@(TCon (TConDataType name)) = case lookupMap name $ typeEnvSynonyms env of
      Just t2 -> normalize strict t2
      Nothing -> if strict then TStrict t1 else t1
    normalize True t1 = TStrict t1
    normalize False t1 = t1

typeOfId :: TypeEnvironment -> Id -> Type
typeOfId env name = case lookupMap name $ typeEnvGlobalValues env of
  Just tp -> tp
  Nothing -> case lookupMap name $ typeEnvLocalValues env of
    Just tp -> tp
    Nothing -> internalError "Core.TypeEnvironment" "typeOfId" $ "variable " ++ show name ++ " not found in type environment"

typeOfCoreExpression :: TypeEnvironment -> Bool -> Expr -> Type

-- Find type of the expression in the Let
typeOfCoreExpression env a (Let binds expr)
  = typeOfCoreExpression (typeEnvAddBinds binds env) a expr

-- All Alternatives of a Match should have the same return type,
-- so we only have to check the first one.
typeOfCoreExpression env False (Match name (Alt pattern expr : _))
  = typeOfCoreExpression (typeEnvAddPattern pattern env) False expr

-- Annotations have to be unified because all branches
-- need to match one annotation.
typeOfCoreExpression env True (Match name (alt : alts))
  = foldr unifyAnnotations baseType alts'
  where
    baseType = typeOfCoreAlt env alt
    alts' = map (typeOfCoreAlt env) alts
    typeOfCoreAlt env (Alt pattern expr) = typeOfCoreExpression (typeEnvAddPattern pattern env) True expr

-- Expression: e1 e2
-- Resolve the type of e1, which should be a function type.
typeOfCoreExpression env a e@(Ap e1 e2) = case typeNotStrict $ typeNormalizeHead env $ typeOfCoreExpression env a e1 of
  TAp (TAp (TCon TConFun) _) tReturn -> tReturn
  tp -> internalError "Core.TypeEnvironment" "typeOfCoreExpression" $ "expected a function type in the first argument of a function application, got " ++ showType [] tp ++ " in expression " ++ show (pretty e)

-- Expression: e1 { tp1 }
-- The type of e1 should be of the form `forall x. tp2`. Substitute x with tp1 in tp2.
typeOfCoreExpression env a (ApType e1 tp1) = case tp1 of
    t@(TAnn _) -> fst $ annApplyList (typeOfCoreExpression env a e1) [t] env
    _ -> case typeNormalizeHead env $ typeOfCoreExpression env a e1 of
      tp@(TForall _ _ _) -> typeApply tp tp1
      tp -> internalError "Core.TypeEnvironment" "typeOfCoreExpression" $ "typeOfCoreExpression: expected a forall type in the first argument of a function application, got " ++ showType [] tp

-- Expression: \x: t1 -> e
-- If e has type t2, then the lambda has type t1 -> t2
typeOfCoreExpression env a (Lam _ var@(Variable _ tp) expr) =
  typeFunction [tp] $ typeOfCoreExpression env' a expr
  where
    env' = typeEnvAddVariable var env

-- Expression: forall x. expr
-- If expr has type t, then the forall expression has type `forall x. t`.
typeOfCoreExpression env a (Forall x kind expr) =
  TForall x kind $ typeOfCoreExpression (typeEnvWeaken 1 env) a expr

-- Expression: (,)
-- Type: forall a. forall b. a -> b -> (a, b)
typeOfCoreExpression env a (Con (ConTuple arity)) = typeTuple arity a

-- Resolve the type of a variable or constructor
typeOfCoreExpression env _ (Con (ConId x)) = typeOfId env x
typeOfCoreExpression env _ (Var x) = typeOfId env x

-- Types of literals
typeOfCoreExpression _ _ (Lit lit) = typeOfLiteral lit

-- Place L annotations in tuple if the type has to be annotated
typeTuple :: Int -> Bool -> Type
typeTuple arity a = foldr (\var -> TForall (Quantor Nothing) KStar) (if a then annotate tf else tf) vars
  where
    tf = typeFunction (map TVar vars) tp
    -- Type without quantifications, eg (a, b)
    tp = foldl (\t var -> TAp t $ TVar var) (TCon $ TConTuple arity) vars
    vars = reverse [0 .. arity - 1]
    annotate :: Type -> Type
    annotate (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) (TAp (TAnn L) (TAp (TAnn L) (TAp (TAnn L) t1)))) $ annotate t2
    annotate t = t

typeEqual :: TypeEnvironment -> Type -> Type -> Bool
typeEqual env = typeEqual' env True

typeEqualIgnoreStrictness :: TypeEnvironment -> Type -> Type -> Bool
typeEqualIgnoreStrictness env = typeEqual' env False

-- Checks type equivalence
typeEqual' :: TypeEnvironment -> Bool -> Type -> Type -> Bool
typeEqual' env False (TStrict t1) t2 = typeEqual' env False t1 t2 -- Ignore strictness
typeEqual' env False t1 (TStrict t2) = typeEqual' env False t1 t2 -- Ignore strictness
typeEqual' env True (TStrict t1) (TStrict t2) = typeEqual' env True t1 t2 -- Do use strictness
typeEqual' env _ (TVar x1) (TVar x2) = x1 == x2
typeEqual' env checkStrict t1@(TCon _) t2 = typeEqualNoTypeSynonym env checkStrict (typeNormalizeHead env t1) (typeNormalizeHead env t2)
typeEqual' env checkStrict t1 t2@(TCon _) = typeEqualNoTypeSynonym env checkStrict (typeNormalizeHead env t1) (typeNormalizeHead env t2)
typeEqual' env checkStrict t1@(TAp _ _) t2 = typeEqualNoTypeSynonym env checkStrict (typeNormalizeHead env t1) (typeNormalizeHead env t2)
typeEqual' env checkStrict t1 t2@(TAp _ _) = typeEqualNoTypeSynonym env checkStrict (typeNormalizeHead env t1) (typeNormalizeHead env t2)
typeEqual' env checkStrict (TForall _ _ t1) (TForall _ _ t2) =
  typeEqual' env checkStrict t1 t2
typeEqual' env _ _ _ = False

-- Checks type equivalence, assuming that there is no synonym at the head of the type
typeEqualNoTypeSynonym :: TypeEnvironment -> Bool -> Type -> Type -> Bool
typeEqualNoTypeSynonym env checkStrict (TAp tl1 tl2) (TAp tr1 tr2)
  = typeEqualNoTypeSynonym env checkStrict tl1 tr1
  && typeEqual' env checkStrict tl2 tr2
typeEqualNoTypeSynonym _ _ (TAp _ _) _ = False
typeEqualNoTypeSynonym _ _ _ (TAp _ _) = False
typeEqualNoTypeSynonym _ _ (TCon c1) (TCon c2) = c1 == c2
typeEqualNoTypeSynonym _ _ (TCon _) _ = False
typeEqualNoTypeSynonym _ _ _ (TCon _) = False
typeEqualNoTypeSynonym env checkStrict t1 t2 = typeEqual' env checkStrict t1 t2

typeOfLiteral :: Literal -> Type
typeOfLiteral (LitInt _ tp) = TCon $ TConDataType $ idFromString $ show tp
typeOfLiteral (LitDouble _) = TCon $ TConDataType $ idFromString "Double"
typeOfLiteral (LitBytes _) = TCon $ TConDataType $ idFromString "String"

data FunctionType = FunctionType { functionArguments :: ![Either Quantor Type], functionReturnType :: !Type }
  deriving (Eq, Ord)

functionArity :: FunctionType -> Arity
functionArity (FunctionType args _) = length $ rights args

typeFromFunctionType :: FunctionType -> Type
typeFromFunctionType (FunctionType args ret) = foldr addArg ret args
  where
    addArg (Left quantor) = TForall quantor KStar
    addArg (Right tp) = TAp $ TAp (TCon $ TConFun) tp

extractFunctionTypeNoSynonyms :: Type -> FunctionType
extractFunctionTypeNoSynonyms (TForall quantor _ tp) = FunctionType (Left quantor : args) ret
  where
    FunctionType args ret = extractFunctionTypeNoSynonyms tp
extractFunctionTypeNoSynonyms (TAp (TAp (TCon TConFun) tArg) tReturn) = FunctionType (Right tArg : args) ret
  where
    FunctionType args ret = extractFunctionTypeNoSynonyms tReturn
extractFunctionTypeNoSynonyms tp = FunctionType [] tp

extractFunctionTypeWithArityNoSynonyms :: Int -> Type -> Maybe FunctionType
extractFunctionTypeWithArityNoSynonyms 0 tp = Just $ FunctionType [] tp
extractFunctionTypeWithArityNoSynonyms arity (TForall quantor _ tp') = do
    FunctionType args ret <- extractFunctionTypeWithArityNoSynonyms arity tp'
    return $ FunctionType (Left quantor : args) ret
extractFunctionTypeWithArityNoSynonyms arity (TAp (TAp (TCon TConFun) tArg) tReturn) = do
    FunctionType args ret <- extractFunctionTypeWithArityNoSynonyms (arity - 1) tReturn
    return $ FunctionType (Right tArg : args) ret
extractFunctionTypeWithArityNoSynonyms _ _ = Nothing

extractFunctionTypeWithArity :: TypeEnvironment -> Int -> Type -> FunctionType
extractFunctionTypeWithArity _ 0 tp = FunctionType [] tp
extractFunctionTypeWithArity env arity tp = case typeNormalizeHead env tp of
  TStrict tp' -> extractFunctionTypeWithArity env arity tp'
  TForall quantor _ tp' ->
    let FunctionType args ret = extractFunctionTypeWithArity env arity tp'
    in FunctionType (Left quantor : args) ret
  TAp (TAp (TCon TConFun) tArg) tReturn ->
    let FunctionType args ret = extractFunctionTypeWithArity env (arity - 1) tReturn
    in FunctionType (Right tArg : args) ret
  _ -> error ("extractFunctionTypeWithArity: expected function type or forall type, got " ++ showType [] tp)

updateFunctionTypeStrictness :: TypeEnvironment -> [Bool] -> Type -> Type
updateFunctionTypeStrictness _ strictness tp
  | all not strictness = tp -- No arguments are strict, type does not change
updateFunctionTypeStrictness env (strict : strictness) tp = case typeNormalizeHead env tp of
  TForall quantor kind tp' -> TForall quantor kind $ updateFunctionTypeStrictness env (strict : strictness) tp'
  TAp (TAp (TCon TConFun) tArg) tReturn ->
    let
      tArg'
        | strict = typeToStrict tArg
        | otherwise = tArg
    in
      TAp (TAp (TCon TConFun) tArg')
        $ updateFunctionTypeStrictness env strictness tReturn
  _ -> error "updateFunctionTypeStrictness: expected function type"

-- Unify the annotations on function arrows with a join
unifyAnnotations :: Type -> Type -> Type
unifyAnnotations (TAp t11 t12) (TAp t21 t22) = TAp t1 t2
  where
    t1 = unifyAnnotations t11 t21
    t2 = unifyAnnotations t12 t22
unifyAnnotations (TStrict t1) t2 = unifyAnnotations t1 t2
unifyAnnotations t1 (TStrict t2) = unifyAnnotations t1 t2
unifyAnnotations (TForall _ _ t1) (TForall q k t2) = TForall q k $ unifyAnnotations t1 t2
unifyAnnotations (TAnn a1) (TAnn a2) = TAnn (join a1 a2)
unifyAnnotations t1 t2 = t2

annSubstitute :: Type -> Quantor -> SAnn -> TypeEnvironment -> Type
annSubstitute (TAp t1 t2) q a env = TAp (annSubstitute t1 q a env) (annSubstitute t2 q a env)
annSubstitute (TForall q' k t) q a env
  | q' == q   = annSubstitute t q a env
  | otherwise = TForall q' k $ annSubstitute t q a env
annSubstitute (TStrict t) q a env = TStrict $ annSubstitute t q a env
annSubstitute (TAnn a') (Quantor (Just id)) a _ = TAnn $ substitueAnn a' id a
annSubstitute t q a env
  | t' == t   = t
  | otherwise = annSubstitute t' q a env
    where
      t' = typeNormalizeHead env t

annApplyList :: Type -> [Type] -> TypeEnvironment -> (Type, [Type])
annApplyList t ((TAnn a):ts) env = annApplyList' t a ts env
annApplyList t ts env = (t, ts)

annApplyList' :: Type -> SAnn -> [Type] -> TypeEnvironment -> (Type, [Type])
annApplyList' (TForall q KAnn t) a ts env = annApplyList (annSubstitute t q a env) ts env
annApplyList' (TForall q k t) a ts env = (TForall q k t', ts')
  where
    (t', ts') = annApplyList' t a ts env
annApplyList' (TStrict t) a ts env = (TStrict t', ts')
  where
    (t', ts') = annApplyList' t a ts env
annApplyList' (TAp t1 t2) a ts env = (TAp t1' t2', ts'')
  where
    (t1', ts') = annApplyList' t1 a ts env
    (t2', ts'') = annApplyList' t2 a ts' env
annApplyList' t a ts env
  | t /= t' = annApplyList' t' a ts env
  | otherwise = (t, ts)
    where
      t' = typeNormalizeHead env t
