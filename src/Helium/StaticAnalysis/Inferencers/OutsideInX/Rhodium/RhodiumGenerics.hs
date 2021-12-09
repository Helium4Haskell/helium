{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumGenerics where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU

import Top.Types.Classes

import Unbound.Generics.LocallyNameless as UB
-- import Unbound.Generics.LocallyNameless.Fresh as UB
-- import Unbound.Generics.LocallyNameless.Alpha as UB
-- --import Unbound.Generics.LocallyNameless.Types as UB
-- import Unbound.Generics.LocallyNameless.Subst as UB

import qualified Data.Map as M

import Data.Maybe
 
addConstraint :: Constraint ConstraintInfo -> PolyType ConstraintInfo -> PolyType ConstraintInfo
addConstraint c p = runFreshM $ addConstraint' c p

addConstraint' :: Constraint ConstraintInfo -> PolyType ConstraintInfo -> UB.FreshM (PolyType ConstraintInfo)
addConstraint' c (PolyType_Mono cs mt) = return $ PolyType_Mono (c:cs) mt
addConstraint' c p@(PolyType_Bind s b) = do
    (t, p) <- unbind b
    p' <- addConstraint' c p
    return $ PolyType_Bind s (bind t p')


expandClassPredicate :: ClassEnvironment -> Constraint ConstraintInfo -> [Constraint ConstraintInfo]
expandClassPredicate env c@(Constraint_Class s vars _) = c : maybe [] (\(supers, _) -> concatMap (\super -> expandClassPredicate env (Constraint_Class super vars Nothing)) supers) (M.lookup s env)
expandClassPredicate _ c = [c]
    

expandClassPredicates  :: ClassEnvironment -> PolyType ConstraintInfo -> PolyType ConstraintInfo
expandClassPredicates = (runFreshM .) . expandClassPredicates'

expandClassPredicates'  :: ClassEnvironment -> PolyType ConstraintInfo -> UB.FreshM (PolyType ConstraintInfo)
expandClassPredicates' env (PolyType_Bind s b) = do
            (t, p) <- unbind b
            p' <- expandClassPredicates' env p
            return $ PolyType_Bind s (bind t p')
expandClassPredicates' env (PolyType_Mono cs m) = return $ PolyType_Mono (concatMap (expandClassPredicate env) cs) m
