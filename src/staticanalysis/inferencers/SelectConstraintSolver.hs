{-| Module      :  SelectConstraintSolver
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Select the type constraint solver of your own liking
-}

module SelectConstraintSolver (selectConstraintSolver) where

import Args (Option(..))
import ConstraintInfo
import TypeConstraints
import ListOfHeuristics (listOfHeuristics)
import ImportEnvironment (ImportEnvironment, getSiblings)
import Top.Types
import Top.States.BasicState (updateErrorInfo)
import Top.States.SubstState (makeSubstConsistent)
import Top.Solvers.SolveConstraints
import Top.States.States
import Top.Solvers.SimpleSolver (runSimple)
import Top.Solvers.GreedySolver (runGreedy)
import Top.TypeGraph.TypeGraphSolver (runTypeGraphPlusDoAtEnd)
import Top.ComposedSolvers.Tree (Tree, spreadTree, phaseTree, chunkTree, flattenTree)
import Top.ComposedSolvers.TreeWalk
import Top.ComposedSolvers.CombinationSolver ((|>>|))
import Top.ComposedSolvers.ChunkySolver (solveChunkConstraints)
--- needed for warnForTooSpecificSignatures
import UHA_Syntax (Name)
import UHA_Utils (NameWithRange(..), nameWithRangeToName)
import Top.Constraints.ExtraConstraints (ExtraConstraint(..))
import Warnings
import Data.Maybe
import Data.List

type TreeSolver = ClassEnvironment -> OrderedTypeSynonyms -> Int 
                       -> Tree (TypeConstraint ConstraintInfo) -> (SolveResult ConstraintInfo Predicates Warnings)

selectConstraintSolver :: [Option] -> ImportEnvironment -> TreeSolver
selectConstraintSolver options importenv classEnv synonyms unique constraintTree =
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
       
       phases       = phaseTree (TCOper "MakeConsistent" makeSubstConsistent)	
       flattening   = flattenTree selectedTreeWalk . phases . spreadingOrNot
       
       constraints      = flattening constraintTree
       chunkConstraints = chunkTree . phases . spreadTree spreadFunction $ constraintTree
       siblings         = getSiblings importenv
       
       selectedSolver
          | SolverSimple      `elem` options = runSimple
          | SolverGreedy      `elem` options = runGreedy                                                        
          | SolverTypeGraph   `elem` options = typegraphSolver
          | SolverCombination `elem` options = combinedSolver             
          | otherwise = \classEnv synonyms unique _ ->  
              solveChunkConstraints polySubst combinedSolver (flattenTree selectedTreeWalk) classEnv synonyms unique chunkConstraints
      
       typegraphSolver =
          let heuristics = listOfHeuristics options siblings
          in runTypeGraphPlusDoAtEnd heuristics (return ())

       combinedSolver =
          (if SignatureWarnings `elem` options then warnForTooSpecificSignatures runGreedy else runGreedy)   
             |>>| typegraphSolver
   in 
      selectedSolver classEnv synonyms unique constraints

warnForTooSpecificSignatures :: SolverX (TypeConstraint ConstraintInfo) ConstraintInfo Predicates Warnings -> SolverX (TypeConstraint ConstraintInfo) ConstraintInfo Predicates Warnings
warnForTooSpecificSignatures solver classEnv synonyms unique constraints =
   let -- split the constraints that come from an explicit type signature from the others.
       -- (only for the definition, not for the uses)
       (explicits, normalConstraints) = partition (isJust . maybeExplicitlyTyped) constraints
       -- make new (equality) constraints for the explicits
       newConstraints = concatMap makeNewConstraint
                      . groupBy (\x y -> fst x    ==     fst y)
                      . sortBy  (\x y -> fst x `compare` fst y)
                      $ map (fromJust . maybeExplicitlyTyped) explicits
       
       -- first solve the new constraint set and the "normal" constraints. Try to determine an "inferred" and more general
       -- type from this result. Then, solve the explicit constraints that were left out to make the final substitution as
       -- it would be originally.
       result1 = solver classEnv synonyms unique (newConstraints ++ normalConstraints)
       result2 = solver classEnv synonyms (uniqueFromResult result1) (substitutionFromResult result1 |-> explicits)
       
       -- make the warnings
       warnings = [] {- -- disabled for the moment -- 
          let f (monos, name, tp, signature) =
                 let ms  = substitutionFromResult result1 |-> monos
                     ps  = predictesFromResult result1 
                     ts  = makeScheme (ftv ms) ps (substitutionFromResult result1 |-> tp)
                     b1  = genericInstanceOf synonyms classEnv signature ts
                     b2  = genericInstanceOf synonyms classEnv ts signature
                 in [ SignatureTooSpecific name signature ts | b1 && not b2 ] 

          in [ warning | Just x <- map splitExplicit explicits, warning <- f x ]    -}     
       
   in (result1 { extensionFromResult = warnings ++ extensionFromResult result1 }) `plus` result2

 where 
   makeNewConstraint :: [(NameWithRange, Tp)] -> [TypeConstraint ConstraintInfo]
   makeNewConstraint [] = []
   makeNewConstraint ((name, t1):rest) = 
      let info = cinfoSameBindingGroup (nameWithRangeToName name)
      in [ (t1 .==. t2) info | (_, t2) <- rest ]

   maybeExplicitlyTyped :: TypeConstraint ConstraintInfo -> Maybe (NameWithRange, Tp)
   maybeExplicitlyTyped (TC2 (Instantiate tp _ info)) = 
      do (monos, name) <- maybeExplicitTypedDefinition info
         return (NameWithRange name, tp)
   maybeExplicitlyTyped _ = Nothing
         
   splitExplicit :: TypeConstraint ConstraintInfo -> Maybe (Tps, Name, Tp, TpScheme)
   splitExplicit (TC2 (Instantiate tp (SigmaScheme tpscheme) info))
      | isExplicitTypedBinding info =
           do (monos, name) <- maybeExplicitTypedDefinition info
              return (monos, name, tp, tpscheme)
   splitExplicit _ = Nothing
   
instance Show Warning where show _ = "<warning>"
instance IsState Warnings