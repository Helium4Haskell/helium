{-# LANGUAGE UndecidableInstances, FlexibleContexts #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
-----------------------------------------------------------------------------

module Helium.Top.Top.Solver.TypeGraph where

import Helium.Top.Top.Solver
import Helium.Top.Top.Constraint
import Helium.Top.Top.Constraint.Information
import Helium.Top.Top.Interface.Substitution()
import Helium.Top.Top.Implementation.General
import Helium.Top.Top.Implementation.Basic
import Helium.Top.Top.Implementation.Overloading
import Helium.Top.Top.Implementation.TypeInference
import Helium.Top.Top.Implementation.TypeGraphSubstitution
import Helium.Top.Top.Implementation.TypeGraph.Heuristic
import Helium.Top.Top.Monad.Select

type TG  info = BasicMonad (TGS info)
type TGS info = And ( Fix (BasicState info) ) 
                        ( And ( Simple (TIState info) ) 
                              ( And ( Simple (TypeGraphState info) ) 
                                    ( Simple (OverloadingState info) )
                              )
                        )

solveTypeGraph :: (Solvable constraint (TG info), TypeConstraintInfo info) 
                     => TG info () -> SolveOptions info -> [constraint] -> TG info (SolveResult info)
solveTypeGraph m options cs =
   do initialize cs options >> m
      onlySolveConstraints cs
      solveResult

typegraphConstraintSolver :: (TypeConstraintInfo info, Solvable constraint (TG info)) 
                                => PathHeuristics info -> ConstraintSolver constraint info
typegraphConstraintSolver hs = 
   let setHeuristics = deselect (modify (\tgs -> tgs { heuristics = hs }))
   in makeConstraintSolver (solveTypeGraph setHeuristics)

typegraphConstraintSolverDefault :: (TypeConstraintInfo info, Solvable constraint (TG info)) 
                                       => ConstraintSolver constraint info
typegraphConstraintSolverDefault = 
   makeConstraintSolver (solveTypeGraph (return ()))

---
{-
cs = [ TVar 0 .==. (TVar 1 .->. TVar 1) $ "a" 
     , TVar 0 .==. (TVar 2 .->. TVar 3) $ "b"
     , TVar 2 .==. intType $ "c" 
     , TVar 3 .==. boolType $ "d" 
     ]
     
test = let (a, b) = solve (solveOptions {uniqueCounter = 4}) cs typegraphConstraintSolverDefault
       in (b, errorsFromResult a) -}