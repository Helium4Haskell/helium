module InfiniteTypeHeuristic where

import SolveConstraints
import SolveEquivalenceGroups
import SolveTypeGraph
import TypeGraphConstraintInfo

import List   (nub, maximumBy, minimumBy)
import Maybe  (catMaybes)
import Utils  (internalError)

infiniteTypeHeuristic :: (TypeGraph EquivalenceGroups info, TypeGraphConstraintInfo info, Show info) =>  
                          [Int] -> SolveState EquivalenceGroups info ([EdgeID], [info])
infiniteTypeHeuristic is = 
   do addDebug (putStrLn "Infinite Type") 
      
      infinitePaths <- mapM infinitePaths is
      
      pathsList <- let f path     = mapM g (shift path) 
                       g (v1, v2) = getPathsFrom v1 [v2]
                   in mapM f . nub . map rotateToNormalForm . concat $ infinitePaths
      
      let onlyInitialEdges path = [ (edge, info) | (edge, Initial info) <- path ] 
          
          compareInfosMax = compareInfos id
          compareInfosMin = compareInfos negate
          
          compareInfos phaseFunction (edge1, info1) (edge2, info2) =
             let f x = ( maybe 0 phaseFunction (getConstraintPhaseNumber x) 
                       , maybe 0 id (getPosition x)
                       )  
             in f info1 `compare` f info2
                                                     
          result = safeMinimumBy compareInfosMin
                 . catMaybes 
                 . map ( safeMaximumBy compareInfosMax
                       . catMaybes
                       . map ( safeMinimumBy compareInfosMin                                
                             . catMaybes
                             . map ( safeMaximumBy compareInfosMax
                                   . onlyInitialEdges
                                   )
                             )      
                       )
                 $ pathsList

      case result of 
         Just (edge, info) -> return ([edge], [info])
         Nothing           -> internalError "TypeGraphHeuristics" 
                                            "heuristicsInfiniteType" 
                                            "could not return a result"

shift :: [(a,a)] -> [(a,a)]
shift []                 = []
shift [(a,b)]            = [(b,a)]
shift ((a,b):(c,d):rest) = (b,c) : shift ((a,d):rest)

rotateToNormalForm :: Ord a => [(a, b)] -> [(a, b)]
rotateToNormalForm [] = []
rotateToNormalForm xs = let minValue = minimum (map fst xs)
                            (as, bs) = span ((minValue /=) . fst) xs
                        in bs ++ as

safeMaximumBy :: (a -> a -> Ordering) -> [a] -> Maybe a
safeMaximumBy f xs 
   | null xs   = Nothing
   | otherwise = Just (maximumBy f xs)

safeMinimumBy :: (a -> a -> Ordering) -> [a] -> Maybe a
safeMinimumBy f xs 
   | null xs   = Nothing
   | otherwise = Just (minimumBy f xs)
