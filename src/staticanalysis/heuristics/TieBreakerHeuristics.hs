-----------------------------------------------------------------------------
-- |The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A tie-breaker heuristic will be used if all other heuristics cannot decide on
-- which error to report. 
--
-----------------------------------------------------------------------------

module TieBreakerHeuristics where

import Top.TypeGraph.Heuristics

-----------------------------------------------------------------------------

class HasTrustFactor a where
   trustFactor :: a -> Float

trustFactorOfConstraint :: HasTrustFactor info => Heuristic info
trustFactorOfConstraint = 
   Heuristic (
      let f (_, _, info) = return (trustFactor info)
      in minimalEdgeFilter "Trust factor of edge" f)

-----------------------------------------------------------------------------

class HasDirection a where
   isTopDown :: a -> Bool

-- note: because True > False, we use the minimal edge filter to keep
--       all the top down edges
isTopDownEdge :: HasDirection info => Heuristic info
isTopDownEdge = 
   Heuristic (
      let f (_, _, info) = return (isTopDown info)
      in minimalEdgeFilter "Is a top down edge" f)

-----------------------------------------------------------------------------
