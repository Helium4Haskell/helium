module Helium.CodeGeneration.Core.Strictness.Instantiate (instantiateDeclaration) where

import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

simplify :: (Expr, Type) -> NameSupply -> TypeEnvironment -> (Expr, Type)
simplify (e, t) supply env = (e', t')
    where
      e' = instantiateExpression env supply e
      cs = analyseValue env (e', t)
      sc = solveConstraints cs
      t' = forallify $ transformType sc True False t

simplifyRec :: [(Expr, Type, Id)] -> NameSupply -> TypeEnvironment -> [(Expr, Type, Id)]
simplifyRec xs supply env = zipWith (\(_, t) (e, _, x) -> (e, t, x)) tds ids'
    where
        env' = typeEnvAddGlobalValues (map (\(_, t, x) -> (x, t)) xs) env
        ids = mapWithSupply (\s (e, t, x) -> (instantiateExpression env' s e, t, x)) supply xs
        -- Analyse declarations
        cs = map (\(e, t, _) -> analyseValue env' (e, t)) ids
        -- Solve constraints
        sc = solveConstraints (S.unions cs)
        -- Apply transformations
        tds = map (\(_, t, x) -> (x, forallify $ transformType sc True False t)) ids
        env'' = typeEnvAddGlobalValues tds env
        -- Instantiate again but now with forallified types
        ids' = mapWithSupply (\s (e, t, x) -> (instantiateExpression env'' s e, t, x)) supply xs


-- Instantiate declaration
instantiateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
instantiateDeclaration env supply decl@DeclValue{} = decl{valueValue = v}
    where
        v = instantiateExpression env supply $ valueValue decl
instantiateDeclaration _ _ decl@DeclAbstract{} = decl{declType = forallify $ declType decl}
instantiateDeclaration _ _ decl@DeclCon{} = decl{declType = forallify $ declType decl}
instantiateDeclaration _ _ decl@DeclTypeSynonym{} = decl{declType = forallify $ declType decl}
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
instantiateExpression env supply (Lam s v e) = Lam s v e'
    where
        e' = instantiateExpression (typeEnvAddVariable v env) supply e
instantiateExpression env supply (Forall q k e) = Forall q k $ instantiateExpression env supply e
instantiateExpression env supply e@(Var v) = instantiate env supply v e
instantiateExpression env supply e@(Con (ConId c)) = instantiate env supply c e
instantiateExpression _ _ e = e -- Lit and Tuple

-- Instantiate binds
instantiateBinds :: TypeEnvironment -> NameSupply -> Binds -> Binds
instantiateBinds env supply (Strict b) = Strict $ instantiateBind env supply b
instantiateBinds env supply (NonRec b) = NonRec $ instantiateBind env supply b
instantiateBinds env supply (Rec bs)   = Rec bs''
    where
        bs' = map (\(Bind (Variable x t) e) -> (e, t, x)) bs
        bs'' = map (\(e, t, x) -> Bind (Variable x t) e) $ simplifyRec bs' supply env

-- Instantiate bind
instantiateBind :: TypeEnvironment -> NameSupply -> Bind -> Bind
instantiateBind env supply (Bind (Variable x (TAp a1 (TAp r (TAp a2 t)))) e) = Bind (Variable x (TAp a1 (TAp r (TAp a2 t')))) e'
    where
        (e', t') = simplify (e, t) supply env

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
        n = getVariablesType $ typeOfId env c
instantiatePat _ _ p = p

-- Instantiate variable or constructor
instantiate :: TypeEnvironment -> NameSupply -> Id -> Expr -> Expr
instantiate env supply id e = foldr (\x e' -> ApType e' (TAnn (AnnVar x))) e ids
    where
        -- Get all foralls, add an ApType with fresh variable
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply $ getForalls (typeOfId env id)
        getForalls :: Type -> [Bool]
        getForalls (TForall _ KAnn t) = True : getForalls t
        getForalls (TForall _ _ t) = getForalls t
        getForalls (TStrict t) = getForalls t
        getForalls (TAp t1 t2) = getForalls t1 ++ getForalls t2
        getForalls t | t' == t = []
                     | otherwise = getForalls t'
                        where
                            t' = typeNormalizeHead env t
