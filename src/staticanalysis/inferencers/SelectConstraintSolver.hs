-----------------------------------------------------------------------------
-- The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Select the type constraint solver of your own liking
--
-----------------------------------------------------------------------------

module SelectConstraintSolver (selectConstraintSolver) where

import Args (Option(..))
import ConstraintInfo (ConstraintInfo)
import TypeConstraints (TypeConstraint(..), spreadFunction, dependencyTypeConstraint)
import ContributingSites (contributingSites)
import ListOfHeuristics (listOfHeuristics)
import ImportEnvironment (ImportEnvironment, getSiblings)
import Top.Types (OrderedTypeSynonyms)
import Top.States.BasicState (updateErrors)
import Top.States.SubstState (makeConsistent)
import Top.Solvers.SolveConstraints (Solver, SolveResult)
import Top.Solvers.SimpleSolver (solveSimple)
import Top.Solvers.GreedySolver (solveGreedy)
import Top.TypeGraph.TypeGraphSolver (solveTypeGraphPlusDoAtEnd)
import Top.ComposedSolvers.Tree (Tree, spreadTree, phaseTree, chunkTree, flattenTree)
import Top.ComposedSolvers.TreeWalk
import Top.ComposedSolvers.CombinationSolver ((|>>|))
import Top.ComposedSolvers.ChunkySolver (solveChunkConstraints)

type TreeSolver constraint info = OrderedTypeSynonyms -> Int -> Tree constraint -> SolveResult info

selectConstraintSolver :: [Option] -> ImportEnvironment -> TreeSolver (TypeConstraint ConstraintInfo) ConstraintInfo
selectConstraintSolver options importenv synonyms unique constraintTree =
   let
       -- spread type constraints or not (i.e., map some type constraints to a 
       -- corresponding node in the constraint tree)
       -- spreading is enabled by default 
       spreadingOrNot 
          | NoSpreading `elem` options = id
          | otherwise                  = spreadTree spreadFunction
	 
       -- choose your treewalk to flatten the constraint tree
       -- the default treewalk is TreeWalkInorderTopLastPost (similar to 'W')
       simpleTreeWalk
          | TreeWalkTopDown             `elem` options = topDownTreeWalk
          | TreeWalkBottomUp            `elem` options = bottomUpTreeWalk
          | TreeWalkInorderTopFirstPre  `elem` options = inorderTopFirstPreTreeWalk
          | TreeWalkInorderTopLastPre   `elem` options = inorderTopLastPreTreeWalk
          | TreeWalkInorderTopFirstPost `elem` options = inorderTopFirstPostTreeWalk
          | otherwise                                  = inorderTopLastPostTreeWalk   
       
       selectedTreeWalk 
          | RightToLeft `elem` options = reverseTreeWalk simpleTreeWalk
          | otherwise                  = simpleTreeWalk
       
       phases      = phaseTree (TC_Oper "MakeConsistent" makeConsistent)	
       flattening  = flattenTree selectedTreeWalk . phases . spreadingOrNot
       
       constraints      = flattening constraintTree
       chunkConstraints = chunkTree dependencyTypeConstraint . phases . spreadTree spreadFunction $ constraintTree
       siblings         = getSiblings importenv
       
       selectedSolver
          | SolverSimple      `elem` options = solveSimple
          | SolverGreedy      `elem` options = solveGreedy                                                         
          | SolverTypeGraph   `elem` options = typegraphSolver
          | SolverCombination `elem` options = combinedSolver             
          | otherwise = \synonyms unique _ ->  
               solveChunkConstraints combinedSolver (flattenTree selectedTreeWalk) synonyms unique chunkConstraints

       typegraphSolver =
          let atEnd | Highlighting `elem` options = updateErrors contributingSites
                    | otherwise                   = return ()
	      heuristics = listOfHeuristics options siblings
	  in solveTypeGraphPlusDoAtEnd heuristics atEnd

       combinedSolver = 
          solveGreedy |>>| typegraphSolver      
   in 
      selectedSolver synonyms unique constraints
