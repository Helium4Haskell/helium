module TieBreakerHeuristics (tieBreakerHeuristics) where

import IsTypeGraph
import TypeGraphConstraintInfo

type TieBreakerHeuristics m info = [TieBreakerHeuristic m info]
type TieBreakerHeuristic  m info = EdgeID -> info -> m (Float, String)

tieBreakerHeuristics :: IsTypeGraph m info => TieBreakerHeuristics m info
tieBreakerHeuristics =
   [ positionInList
   , trustFactorOfConstraint
   , isTopDownEdge
   ]

positionInList :: IsTypeGraph m info => TieBreakerHeuristic m info
positionInList edge info =
   case getPosition info of
      Nothing       -> return (1.0, "position unknown")
      Just position -> let modifier = 1 + fromIntegral position / 10000
                       in return (modifier, "position="++show position)
                       
trustFactorOfConstraint :: IsTypeGraph m info => TieBreakerHeuristic m info
trustFactorOfConstraint edge info =
   let trust    = getTrustFactor info
       modifier = 1 / trust
   in return (modifier, "trustfactor="++show trust)
                    
isTopDownEdge :: IsTypeGraph m info => TieBreakerHeuristic m info
isTopDownEdge edge info 
   | isFolkloreConstraint info = return (0.5, "is a top down edge")
   | otherwise                 = return (1.0, "is not a top down edge")
