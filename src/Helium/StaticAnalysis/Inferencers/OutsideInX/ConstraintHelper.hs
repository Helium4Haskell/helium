module Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper where

import Data.Maybe
import qualified Data.Map as M

import Cobalt.Core

import Top.Types.Classes

import Unbound.LocallyNameless

monotypeTuple :: [MonoType] -> MonoType
monotypeTuple vars = let
    tupleType = "(" ++ replicate (length vars - 1) ',' ++ ")"
    in conApply tupleType vars

monotypeList :: MonoType -> MonoType
monotypeList elem = conApply "[]" [elem] 

expandClassPredicates  :: ClassEnvironment -> PolyType -> PolyType
expandClassPredicates = (runFreshM .) . expandClassPredicates'

expandClassPredicates'  :: ClassEnvironment -> PolyType -> FreshM PolyType
expandClassPredicates' env (PolyType_Bind b) = do
            (t, p) <- unbind b
            p' <- expandClassPredicates' env p
            return $ PolyType_Bind (bind t p')
expandClassPredicates' env (PolyType_Mono cs m) = return $ PolyType_Mono (concatMap (expandClassPredicate env) cs) m

expandClassPredicate :: ClassEnvironment -> Constraint -> [Constraint]
expandClassPredicate env c@(Constraint_Class s vars) = c : maybe [] (\(supers, _) -> concatMap (\super -> expandClassPredicate env (Constraint_Class super vars)) supers) (M.lookup s env)
expandClassPredicate _ c = [c]