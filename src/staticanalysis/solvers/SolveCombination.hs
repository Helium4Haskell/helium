module SolveCombination where

import SolveGreedy
import SolveTypeGraph
import Constraints
import IsTypeGraph
import Types

solveCombination :: ( IsTypeGraph (TypeGraph info) info
                    , SolvableConstraint constraint (Greedy info)
                    , SolvableConstraint constraint (TypeGraph info)
                    , Show constraint
                    ) => (OrderedTypeSynonyms, [[(String, TpScheme)]]) -> Int -> [constraint]  
                      -> (Int, FixpointSubstitution, Predicates, [info], IO ())
solveCombination options@(synonyms, _) unique constraints 
   | null errors = resultGreedy
   | otherwise   = resultTypeGraph
 where resultGreedy@(_, _, _, errors, _) = solveGreedy    synonyms unique constraints
       resultTypeGraph                   = solveTypeGraph options  unique constraints
