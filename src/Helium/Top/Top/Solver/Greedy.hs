{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Solver.Greedy where

import Helium.Top.Top.Interface.Substitution()      
import Helium.Top.Top.Implementation.General
import Helium.Top.Top.Implementation.Basic
import Helium.Top.Top.Implementation.TypeInference
import Helium.Top.Top.Implementation.FastSubstitution
import Helium.Top.Top.Implementation.SimpleSubstitution
import Helium.Top.Top.Implementation.Overloading
import Helium.Top.Top.Solver
import Helium.Top.Top.Constraint
import Helium.Top.Top.Constraint.Information
-- for testing only
-- import Top.Types
-- import Top.Constraint.Equality

type Greedy  info = BasicMonad (GreedyS info)
type GreedyS info = And ( Fix (BasicState info) ) 
                        ( And ( Simple (TIState info) ) 
                              ( And ( Simple (GreedyState info) ) 
                                    ( Simple (OverloadingState info) )
                              )
                        )

solveGreedy :: (Solvable constraint (Greedy info), TypeConstraintInfo info) =>
               SolveOptions info -> [constraint] -> Greedy info (SolveResult info)
solveGreedy = solveConstraints

greedyConstraintSolver :: (TypeConstraintInfo info, Solvable constraint (Greedy info)) => ConstraintSolver constraint info
greedyConstraintSolver = makeConstraintSolver solveGreedy

--------------------------------

type GreedySimple  info = BasicMonad (GreedySimpleS info)
type GreedySimpleS info = And ( Fix (BasicState info) ) 
                              ( And ( Simple (TIState info) ) 
                                    ( And ( Simple (SimpleState info) ) 
                                          ( Simple (OverloadingState info) )
                                    )
                              )

solveSimple :: (Solvable constraint (GreedySimple info), TypeConstraintInfo info) =>
               SolveOptions info -> [constraint] -> GreedySimple info (SolveResult info)
solveSimple = solveConstraints

greedySimpleConstraintSolver :: (TypeConstraintInfo info, Solvable constraint (GreedySimple info)) => ConstraintSolver constraint info
greedySimpleConstraintSolver = makeConstraintSolver solveSimple

--------------------------------
{-
cs :: [EqualityConstraint String]
cs = [ TVar 0 .==. (TVar 1 .->. TVar 1) $ "a" 
     , TVar 0 .==. (TVar 2 .->. TVar 3) $ "b" 
     , TVar 2 .==. intType $ "c" 
     , TVar 3 .==. boolType $ "d" 
     ]

test = let (a, b) = solve (solveOptions {uniqueCounter = 4}) cs greedyConstraintSolver
       in (b, errorsFromResult a)

test2 = let (a, b) = solve (solveOptions {uniqueCounter = 4}) cs greedySimpleConstraintSolver
        in (b, errorsFromResult a) -}