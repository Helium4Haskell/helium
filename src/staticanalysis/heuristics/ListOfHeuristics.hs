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
import ConstraintInfo -- (ConstraintInfo)
import HeuristicsInfo () -- instances
import Top.Types
import Top.TypeGraph.Heuristics
import Top.TypeGraph.DefaultHeuristics
import RepairHeuristics
import UnifierHeuristics
import OnlyResultHeuristics
import TieBreakerHeuristics

-- temporary
import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Paths
import Data.Maybe
import Top.TypeGraph.Basics

listOfHeuristics :: [Option] -> Siblings -> [Heuristic ConstraintInfo]
listOfHeuristics options siblings =
   let is = [ i | SelectConstraintNumber i <- options ]
   in [ selectConstraintNumbers is | not (null is) ]
   ++
   [ highParticipation 1.00
   , phaseFilter
   ] ++
   [ Heuristic (Voting (
        [ siblingFunctions siblings
        , similarLiterals
        , similarNegation
        , applicationEdge
        , tupleEdge
        , fbHasTooManyArguments
        , variableFunction
	, unaryMinus
	, constraintFromUser
        ] ++
        [ unifierVertex | UnifierHeuristics `elem` options ]))
   | NoRepairHeuristics `notElem` options
   ] ++
   [ applicationResult
   , negationResult
   -- , typeVariableInvolved {- I am not convinced yet. Bastiaan -}
   , trustFactorOfConstraint
   , isTopDownEdge
   , positionInList
   ]
   
-- two more heuristics for the Type Inference Directives
-- (move to another module?)
phaseFilter :: Heuristic ConstraintInfo
phaseFilter = Heuristic (
   let f (_, _, info) = return (phaseOfConstraint info)
   in maximalEdgeFilter "Highest phase number" f)

constraintFromUser :: HasTypeGraph m ConstraintInfo => Selector m ConstraintInfo
constraintFromUser = 
   SelectorPath (\path -> 
      SelectorList ("Constraints from .type file", helper path))

 where
   helper path edges = 
      let
          bestEdge = rec path
	  edgeNrs  = [ i | (_, i, _) <- edges ]
 
          rec path =
             case path of
                x :|: y -> f min (rec x) (rec y)
                x :+: y -> f max (rec x) (rec y)
                Step (_, cNR, info) |  isJust (maybeUserConstraint info) && cNR `elem` edgeNrs 
                        -> Just cNR
                _       -> Nothing
	 
          f :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a	    
          f g ma mb = 
             case (ma, mb) of
                (Just a, Just b) -> Just (g a b)
                (Nothing, _    ) -> mb
                _                -> ma
      in 
         case [ tuple | tuple@(_, cNR, _) <- edges, Just cNR == bestEdge ] of
            [] -> return Nothing
            (edgeID, cNR, info):_ -> 
	       let (groupID, number) = maybe (0, 0) id (maybeUserConstraint info)
	           otherEdges = let p info =
		                       case maybeUserConstraint info of
				          Just (a, b) -> a == groupID && b > number
					  Nothing     -> False
		                in [ e | (e, _, i) <- edges, p i ] -- perhaps over all edges!
	       in return . Just $
	             (8, "constraints from .type file", edgeID:otherEdges, [info])
