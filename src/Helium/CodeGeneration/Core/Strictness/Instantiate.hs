module Helium.CodeGeneration.Core.Strictness.Instantiate (instantiateDeclaration, instantiateDeclarations, forallify) where

import Data.List

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

-- Instantiate recursive declarations
instantiateDeclarations :: TypeEnvironment -> NameSupply -> [CoreDecl] -> [CoreDecl]
instantiateDeclarations env supply decls = decls''
    where
        -- Forallify type signatures before instantiating body
        decls' = map (\d -> d{declType = forallify env (declType d)}) decls
        env' = typeEnvAddGlobalValues (map (\d -> (declName d, declType d)) decls') env
        decls'' = mapWithSupply (\s d -> d{valueValue = instantiateExpression env' s $ valueValue d}) supply decls'

-- Instantiate declaration
instantiateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
instantiateDeclaration env supply decl@DeclValue{}    = decl{valueValue = v', declType = t'}
    where
        v' = instantiateExpression env supply $ valueValue decl
        t' = forallify env $ declType decl
instantiateDeclaration env _ decl@DeclAbstract{} = decl{declType = forallify env $ declType decl}
instantiateDeclaration env _ decl@DeclCon{} = decl{declType = forallify env $ declType decl}
instantiateDeclaration env _ decl@DeclTypeSynonym{} = decl{declType = forallify env $ declType decl}
instantiateDeclaration _ _ decl = decl

-- Instantiate expression
instantiateExpression :: TypeEnvironment -> NameSupply -> Expr -> Expr
instantiateExpression env supply (Let b e) = Let b' e'
    where
        (supply1, supply2) = splitNameSupply supply
        b' = instantiateBinds env supply1 b
        e' = instantiateExpression (typeEnvAddBinds b' env) supply2 e
instantiateExpression env supply (Match x a) = Match x $ mapWithSupply (instantiateAlt env) supply a
instantiateExpression env supply (Ap e1 e2) = Ap e1' e2'
    where
        (supply1, supply2) = splitNameSupply supply
        e1' = instantiateExpression env supply1 e1
        e2' = instantiateExpression env supply2 e2
instantiateExpression env supply (ApType e t) = ApType (instantiateExpression env supply e) t
instantiateExpression env supply (Lam s v e) = Lam s v' e'
    where
        v' = instantiateVar env v
        e' = instantiateExpression (typeEnvAddVariable v' env) supply e
instantiateExpression env supply (Forall q k e) = Forall q k $ instantiateExpression env supply e
instantiateExpression env supply e@(Var v) = instantiate env supply v e
instantiateExpression env supply e@(Con (ConId c)) = instantiate env supply c e
instantiateExpression _ _ e = e -- Lit and Tuple

-- Instantiate binds
instantiateBinds :: TypeEnvironment -> NameSupply -> Binds -> Binds
instantiateBinds env supply (Strict b) = Strict $ instantiateBind env supply b
instantiateBinds env supply (NonRec b) = NonRec $ instantiateBind env supply b
instantiateBinds env supply (Rec bs)   = Rec $ mapWithSupply (instantiateBind env') supply bs'
    where
        -- Forallify type signatures before instantiating body
        bs' = map (\(Bind v e) -> Bind (instantiateVar env v) e) bs
        env' = typeEnvAddBinds (Rec bs') env

-- Instantiate bind
instantiateBind :: TypeEnvironment -> NameSupply -> Bind -> Bind
instantiateBind env supply (Bind v e) = Bind v' e'
    where
        v' = instantiateVar env v 
        e' = instantiateExpression env supply e

-- Instantiate alt
instantiateAlt :: TypeEnvironment -> NameSupply -> Alt -> Alt
instantiateAlt env supply (Alt p e) = Alt p' e'
    where
        (supply1, supply2) = splitNameSupply supply
        p' = instantiatePat env supply1 p
        e' = instantiateExpression (typeEnvAddPattern p' env) supply2 e

-- Instantiate pat  
instantiatePat :: TypeEnvironment -> NameSupply -> Pat -> Pat
instantiatePat env supply (PatCon (ConId c) t i) = PatCon (ConId c) (ids ++ t) i
    where
        -- Add more ids for the extra foralls
        ids = mapWithSupply (\x _ -> TAnn (AnnVar $ fst $ freshId x)) supply n
        n = getVariablesType env $ typeOfId env c
instantiatePat _ _ p = p

-- Instantiate variable
instantiateVar :: TypeEnvironment -> Variable -> Variable
instantiateVar env (Variable x t) = Variable x $ forallify env t

-- Instantiate variable or constructor
instantiate :: TypeEnvironment -> NameSupply -> Id -> Expr -> Expr
instantiate env supply id e = foldr (\x e' -> ApType e' (TAnn (AnnVar x))) e ids
    where
        -- Get all foralls, add an ApType with fresh variable
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply $ getForalls (typeOfId env id)
        getForalls :: Type -> [Bool]
        getForalls (TForall _ KAnn t) = True : getForalls t
        getForalls _ = []

-- Add foralls for strictness annotations
forallify :: TypeEnvironment -> Type -> Type
forallify env (TAp (TAnn a) t) = TAp (TAnn a) $ forallify env t
forallify env t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = getVariablesType env t

getVariablesType :: TypeEnvironment -> Type -> [Id]
getVariablesType env (TAp t1 t2) = nub $ getVariablesType env t1 ++ getVariablesType env t2
getVariablesType env (TStrict t) = getVariablesType env t
getVariablesType env (TForall _ _ t) = getVariablesType env t
getVariablesType _   (TAnn a) = getVariablesAnn a
getVariablesType env t | t' == t   = []
                       | otherwise = getVariablesType env t'
    where
        t' = typeNormalizeHead env t
