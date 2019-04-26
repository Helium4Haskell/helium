module Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper where

import Data.Maybe
import qualified Data.Map as M

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes

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
expandClassPredicates' env (PolyType_Bind s b) = do
            (t, p) <- unbind b
            p' <- expandClassPredicates' env p
            return $ PolyType_Bind s (bind t p')
expandClassPredicates' env (PolyType_Mono cs m) = return $ PolyType_Mono (concatMap (expandClassPredicate env) cs) m

expandClassPredicate :: ClassEnvironment -> Constraint -> [Constraint]
expandClassPredicate env c@(Constraint_Class s vars _) = c : maybe [] (\(supers, _) -> concatMap (\super -> expandClassPredicate env (Constraint_Class super vars Nothing)) supers) (M.lookup s env)
expandClassPredicate _ c = [c]

addConstraint :: Constraint -> PolyType -> PolyType
addConstraint c p = runFreshM $ addConstraint' c p

addConstraint' :: Constraint -> PolyType -> FreshM (PolyType)
addConstraint' c (PolyType_Mono cs mt) = return $ PolyType_Mono (c:cs) mt
addConstraint' c p@(PolyType_Bind s b) = do
   (t, p) <- unbind b
   p' <- addConstraint' c p
   return $ PolyType_Bind s (bind t p')
