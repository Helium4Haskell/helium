-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeGraphHeuristics.hs : Heuristics to make a type graph consistent.
--
-------------------------------------------------------------------------------

module TypeGraphHeuristics where


import Types
import SolveState
import TypeGraphConstraintInfo
import SolveTypeGraph
import IsTypeGraph
import Maybe                    (isJust, isNothing, catMaybes)
import List                     (sortBy, groupBy, find, nub)
import Utils                    (internalError, fst4 )

import Heuristics
import InfiniteTypeHeuristic     
import TieBreakerHeuristics     (tieBreakerHeuristics)
import FilterHeuristics         (filterHeuristics)
import RepairHeuristics         (repairHeuristics)

upperbound_GOODPATHS  =     50 :: Int
upperbound_ERRORPATHS =     50 :: Int

heuristics :: IsTypeGraph (TypeGraph info) info => TypeGraph info ([EdgeID], [info])
heuristics = do conflicts <- getConflicts
                let clashes   = [ i | (ConstantClash, i) <- conflicts ]
                    infinites = [ i | (InfiniteType , i) <- conflicts ]
                if null infinites
                  then heuristicsConstantClash clashes
                  else infiniteTypeHeuristic infinites

heuristicsConstantClash :: IsTypeGraph (TypeGraph info) info => 
              [Int] -> TypeGraph info ([EdgeID], [info])
heuristicsConstantClash is = 

   do pathsWithInfo    <- findPathsInTypeGraph is
      let edgeInfoTable = makeEdgeInfoTable pathsWithInfo
          allEdges      = map fst edgeInfoTable
          
      addDebug . unlines $ 
         ("*** Error Paths in Type Graph ***\n") : 
         zipWith (\i p -> "Path #"++show i++"\n"++replicate 25 '='++"\n"++showPath p) [1..] [ p | (p, (_, _, False)) <- pathsWithInfo ]    

      maxPhaseEdges          <- applyEdgesFilter constraintPhaseFilter allEdges  
      maybeUserConstraint    <- applyEdgesFilter (maybeUserConstraintFilter pathsWithInfo) maxPhaseEdges
      maxDifferentGroupEdges <- applyEdgesFilter (differentGroupsFilter edgeInfoTable) maybeUserConstraint
      
      -- first try heuristics to repair the program
      repairs <- mapM id [ f x y >>= return . fmap (\result -> (result,(x,y)))
                         | 
                           (x, y) <- maxDifferentGroupEdges
                         , f      <- repairHeuristics
                         ]       
      case reverse (sortBy (\((x,_,_),_) ((y,_,_),_) -> x `compare` y) (catMaybes repairs)) of
         
         ((i, actions, msg), (edge, info)) : _ -> 
            do standardEdges <- moreEdgesFromUser info edge
               let (typeError,edgesToRemove) = foldr op (info,standardEdges) actions
                   op action (te,es) = case action of
                                          SetHint h      -> (setNewHint h te,es)
                                          SetTypeError t -> (setNewTypeError t te,es)
                                          RemoveEdge e   -> (te,e:es)
               return (edgesToRemove, [typeError])
         
         [] -> do -- filter some edges 
                  okayEdges <- let edgeFilter edge info = 
                                      do results <- mapM id [ f edge info| f <- filterHeuristics ]
                                         return (all isNothing results)
                               in applyEdgeFilter edgeFilter maxDifferentGroupEdges  

                  -- use tie breaker heuristics
                  bestEdges <- let edgeFilter edge info = 
                                      do results <- mapM id [ f edge info| f <- (errorAndGoodPaths edgeInfoTable) : tieBreakerHeuristics ]
                                         return (product (map fst results))
                               in maximalEdgeFilter edgeFilter okayEdges
                  
                  case bestEdges of
                     []   -> internalError "TypeGraphHeurisitics" "heuristicsConstantClash" "empty list(2)"
                     (edge, info):_ -> 
                        do standardEdges <- moreEdgesFromUser info edge
                           return (standardEdges, [info])

-----------------------------------------------------------

type PathInfo            = ( (Int, Int)  -- (fromVertex, toVertex)
                           , Int         -- equivalence group of clash
                           , Bool        -- correct path?
                           )
type PathInfos           = [PathInfo]
type PathWithInfo cinfo  = (Path cinfo, PathInfo)
type PathsWithInfo cinfo = [PathWithInfo cinfo]
type EdgeInfoTable cinfo = [((EdgeID, cinfo), PathInfos)]

findPathsInTypeGraph :: IsTypeGraph (TypeGraph cinfo) cinfo => [Int] -> TypeGraph cinfo (PathsWithInfo cinfo)
findPathsInTypeGraph is = 
   let 
       rec (gp,ep) []          = return []
       rec (gp,ep) (i:is)      
          | gp <= 0 && ep <= 0 = return []
          | otherwise          = do (rgp1,rep1) <- recGroup (gp,ep) i
                                    recPaths    <- rec (gp - length rgp1,ep - length rep1) is
                                    return (recPaths++rgp1++rep1)                
                                    
       recGroup tuple i =
          let f (gp,ep) []                       = return ([],[])
              f (gp,ep) (((i1,s1),(i2,s2)):rest) 
                 | gp <= 0  && ep <= 0           = return ([],[])  
                 | s1 == s2 && gp <= 0           = f (gp,ep) rest
                 | s1 /= s2 && ep <= 0           = f (gp,ep) rest
                 | otherwise                     = 

                      do paths <- getPathsFrom i1 [i2]
                         if s1 == s2 
                           then do (r1,r2) <- f (gp - length paths,ep) rest
                                   return ([ (path, ((i1,i2),i,True)) | path <- paths ] ++ r1,r2)
                           else do (r1,r2) <- f (gp,ep - length paths) rest
                                   return (r1,[ (path, ((i1,i2),i,False)) | path <- paths ] ++ r2)

          in do vertices <- getVerticesInGroup i
                f tuple (combinations [ (i,s) | (i,(Just s,_,_)) <- vertices ] )  
                
       combinations :: [a] -> [(a,a)]
       combinations []     = []
       combinations (a:as) = zip (repeat a) as ++ combinations as
                                                                                     
   in 
      rec (upperbound_GOODPATHS,upperbound_ERRORPATHS) is

makeEdgeInfoTable :: PathsWithInfo cinfo -> EdgeInfoTable cinfo
makeEdgeInfoTable xs = map (\(e:_, ys) -> (e,ys))
                     . map unzip
                     . groupBy (\x y -> fst (fst x)    ==     fst (fst y))
                     . sortBy  (\x y -> fst (fst x) `compare` fst (fst y))
                     $ [ ((edge,info), pathInfo) | (path, pathInfo) <- xs, (edge,Initial info) <- path ]

         
-----------------------------------------------------------

type EdgesFilter monad cinfo = [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
type EdgeFilter  monad cinfo = EdgeID -> cinfo   -> monad Bool

-- Note: Do not filter away all edges
applyEdgesFilter :: Monad monad => EdgesFilter monad cinfo -> [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
applyEdgesFilter edgesFilter edges = 
   do result <- edgesFilter edges
      return (if null result then edges else result)
   
-- Note: Do not filter away all edges      
applyEdgeFilter :: Monad monad =>  EdgeFilter monad cinfo -> [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
applyEdgeFilter edgeFilter edges = 
   do result <- filterM (uncurry edgeFilter) edges
      return (if null result then edges else result)

maximalEdgeFilter :: (Monad monad, Ord result) => (EdgeID -> cinfo -> monad result) -> EdgesFilter monad cinfo
maximalEdgeFilter function edges = 
   do tupledList <- let f tuple@(edgeID, cinfo) = do result <- function edgeID cinfo
                                                     return (result, tuple)
                    in mapM f edges
      let maximumResult = maximum (map fst tupledList)
      return (map snd (filter ((maximumResult ==) . fst) tupledList))
      
constraintPhaseFilter :: (Monad monad, TypeGraphConstraintInfo cinfo) => EdgesFilter monad cinfo
constraintPhaseFilter = maximalEdgeFilter (const (return . maybe 0 id . getConstraintPhaseNumber))

differentGroupsFilter :: Monad monad => EdgeInfoTable cinfo -> EdgesFilter monad cinfo
differentGroupsFilter edgeInfoTable = maximalEdgeFilter f
   where f edgeID cinfo = return $
            case find ((edgeID==) . fst . fst) edgeInfoTable of 
               Nothing            -> 0
               Just (_,pathInfos) -> length $ nub $ [ grp | (_, grp, False) <- pathInfos ]
               
errorAndGoodPaths :: EdgeInfoTable cinfo -> EdgeID -> info -> TypeGraph info (Float, String)
errorAndGoodPaths edgeInfoTable edgeID cinfo = 
   return $ case find ((edgeID==) . fst . fst) edgeInfoTable of 
      Nothing            -> (1.0, "error and good paths are unknown")
      Just (_,pathInfos) -> 
         let inGoodPaths     = length $ nub $ [ reorder src | (src, _, True ) <- pathInfos ]
             inErrorPaths    = length $ nub $ [ reorder src | (src, _, False) <- pathInfos ]
             reorder (a,b)   = if a <= b then (a,b) else (b,a)
         in (0.1 ^ inGoodPaths * 5.0 ^ inErrorPaths, "[good="++show inGoodPaths ++",error="++show inErrorPaths++"]")
         
maybeUserConstraintFilter :: (Monad monad, TypeGraphConstraintInfo cinfo) => PathsWithInfo cinfo -> EdgesFilter monad cinfo
maybeUserConstraintFilter pathsWithInfo edges = 
   let errorPaths = [ path | (path, (_, _, False)) <- pathsWithInfo ]
       filterForPath path =  [ (edge, info) 
                             | (edge, Initial info) <- path
                             , edge `elem` map fst edges 
                             , isJust (maybeUserConstraint info)
                             ]
       cmp (_, info1) (_, info2) = 
          compare (getPosition info1) (getPosition info2)
   in return 
    . maybe [] (:[]) 
    . safeMinimumBy cmp 
    . catMaybes 
    . map (safeMaximumBy cmp . filterForPath) 
    $ errorPaths