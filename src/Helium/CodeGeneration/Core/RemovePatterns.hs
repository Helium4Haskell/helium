module Helium.CodeGeneration.Core.RemovePatterns (coreRemovePatterns) where

-- Removes unreachable patterns in case expressions (mainly pattern fail errors)
-- Necessary to improve the precision of the strictness analysis
-- Executed between the two let inline passes as the first let inline puts the cases in order making this analysis easier
-- The second pass can then remove unused pattern fail errors in let bindings

import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- For every datatype, a set of constructors
type DataEnvironment = IdMap IdSet
-- For every variable used in a case, the set of constructors yet to match
type MatchEnvironment = IdMap IdSet

coreRemovePatterns :: CoreModule -> CoreModule
coreRemovePatterns mod = mod{moduleDecls = map (analyseDeclaration env typeEnv) $ moduleDecls mod}
    where
        env = foldr insertDeclaration emptyMap $ moduleDecls mod
        typeEnv = typeEnvForModule mod

insertDeclaration :: CoreDecl -> DataEnvironment -> DataEnvironment
insertDeclaration decl@DeclCon{} env = case lookupMap d env of
    -- Data already in environment, add constructor to set
    Just y -> updateMap d (insertSet (declName decl) y) env
    -- Data not in environment, add singleton with constructor
    _      -> insertMap d (singleSet $ declName decl) env
    where
        -- custom "data" x
        [d] = [x | CustomLink x (DeclKindCustom y) <- declCustoms decl, y == idFromString "data"]
insertDeclaration _ env = env

analyseDeclaration :: DataEnvironment -> TypeEnvironment -> CoreDecl -> CoreDecl
analyseDeclaration env typeEnv decl@DeclValue{} = decl{valueValue = analyseExpression env emptyMap typeEnv $ valueValue decl}
analyseDeclaration _ _ decl = decl

analyseExpression :: DataEnvironment -> MatchEnvironment -> TypeEnvironment -> Expr -> Expr
-- let! v :: _ = x in match v with as
analyseExpression env m typeEnv (Let b@(Strict (Bind (Variable v t) (Var x))) (Match id as))
    | v == id = Let b (Match id as')
        where
            as' = analyseAlts env m' typeEnv' x as
            m' = case getData t typeEnv' of
                -- Tuple
                Nothing  -> m
                Just t' -> case lookupMap t' env of
                    -- Char, Int etc.
                    Nothing -> m
                    Just y  -> if elemMap x m then m else insertMap x y m
            typeEnv' = typeEnvAddBinds b typeEnv
analyseExpression env m typeEnv (Let b e) = Let (analyseBinds env m typeEnv b) $ analyseExpression env m typeEnv' e
    where
        typeEnv' = typeEnvAddBinds b typeEnv
analyseExpression env m typeEnv (Match id as) = Match id $ analyseAlts env m' typeEnv id as
    where
        m' = case getData (typeOfId typeEnv id) typeEnv of
            -- Tuple
            Nothing -> m
            Just t' -> case lookupMap t' env of
                -- Char, Int etc.
                Nothing -> m
                Just y  -> insertMap id y m
analyseExpression env m typeEnv (Ap e1 e2) = Ap (analyseExpression env m typeEnv e1) $ analyseExpression env m typeEnv e2
analyseExpression env m typeEnv (ApType e t) = ApType (analyseExpression env m typeEnv e) t
analyseExpression env m typeEnv (Lam s v e) = Lam s v $ analyseExpression env m typeEnv' e
    where
        typeEnv' = typeEnvAddVariable v typeEnv
analyseExpression env m typeEnv (Forall q k e) = Forall q k $ analyseExpression env m typeEnv e
analyseExpression _ _ _ e = e -- Con, Var and Lit

analyseBinds :: DataEnvironment -> MatchEnvironment -> TypeEnvironment -> Binds -> Binds
analyseBinds env m typeEnv (Strict b) = Strict $ analyseBind env m typeEnv b
analyseBinds env m typeEnv (NonRec b) = NonRec $ analyseBind env m typeEnv b
analyseBinds env m typeEnv b@(Rec bs) = Rec $ map (analyseBind env m typeEnv') bs
    where
        typeEnv' = typeEnvAddBinds b typeEnv

analyseBind :: DataEnvironment -> MatchEnvironment -> TypeEnvironment -> Bind -> Bind
analyseBind env m typeEnv (Bind v e) = Bind v $ analyseExpression env m typeEnv e

analyseAlts :: DataEnvironment -> MatchEnvironment -> TypeEnvironment -> Id -> Alts -> Alts
analyseAlts env m typeEnv x (a:as) = case a of
    -- First case is tuple, only that case is enough
    Alt (PatCon (ConTuple _) _ _) _ -> [analyseAlt env m typeEnv a]
    -- Constructor, check if all constructors for datatype have been used
    Alt (PatCon (ConId c) _ _) _ -> if isEmptySet xs 
        -- If so, remove next alts as they are unreachable
        then [analyseAlt env m' typeEnv a]
        -- If not, mark constructor as assigned and keep alts
        else map (analyseAlt env m' typeEnv) (a:as)
            where
                xs = deleteSet c $ findMap x m
                m' = updateMap x xs m
    -- Literal and non-removable default have to stay
    _                               -> map (analyseAlt env m typeEnv) (a:as)
-- Untriggerable case as every alts should have at least one alt, but just in case...
analyseAlts _ _ _ _ [] = []

analyseAlt :: DataEnvironment -> MatchEnvironment -> TypeEnvironment -> Alt -> Alt
analyseAlt env m typeEnv (Alt p e) = Alt p $ analyseExpression env m typeEnv' e
    where
        typeEnv' = typeEnvAddPattern p typeEnv

getData :: Type -> TypeEnvironment -> Maybe Id
getData t typeEnv | t /= t' = getData t' typeEnv
    where
        -- Normalize type in case of typesynonyms
        t' = typeNormalizeHead typeEnv t
getData (TCon (TConDataType n)) _ = Just n
getData (TCon (TConTypeClassDictionary n)) _ = Just n'
    where
        -- Add Dict$ because datatype is stored without it
        n' = idFromString $ "Dict$" ++ stringFromId n
getData (TAp (TAp (TCon TConFun) _) t2) typeEnv = getData t2 typeEnv
getData (TAp t1 _) typeEnv = getData t1 typeEnv
getData (TForall _ _ t) typeEnv = getData t typeEnv
getData (TStrict t) typeEnv = getData t typeEnv
getData _ _ = Nothing -- Tuples need to be handled differently
