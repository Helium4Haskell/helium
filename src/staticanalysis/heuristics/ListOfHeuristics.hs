-----------------------------------------------------------------------------
-- |The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A list of all type graph heuristics that will be used.
--
-----------------------------------------------------------------------------

module ListOfHeuristics (listOfHeuristics) where

import Args (Option(..))
import ConstraintInfo (ConstraintInfo)
import HeuristicsInfo () -- instances
import Top.Types
import Top.TypeGraph.Heuristics
import Top.TypeGraph.DefaultHeuristics
import RepairHeuristics
import UnifierHeuristics
import OnlyResultHeuristics
import TieBreakerHeuristics

listOfHeuristics :: [Option] -> Siblings -> [Heuristic ConstraintInfo]
listOfHeuristics options siblings =
   [ highParticipation 1.00
   ] ++
   [ Heuristic (Voting (
        [ siblingFunctions siblings
        , similarLiterals
        , similarNegation
        , applicationEdge
        , tupleEdge
        , fbHasTooManyArguments
        , variableFunction
        ] ++
        [ unifierVertex | UnifierHeuristics `elem` options ]))
   | NoRepairHeuristics `notElem` options
   ] ++
   [ applicationResult
   , negationResult
   , trustFactorOfConstraint
   , isTopDownEdge
   , positionInList
   ]
