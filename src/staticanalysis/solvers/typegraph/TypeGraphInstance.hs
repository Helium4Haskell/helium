module TypeGraphInstance where

import EquivalenceGroup
import FixpointSolveState
import IsTypeGraph
import List
import Data.STRef
import SolveState
import SolveTypeGraph
import TypeGraphConstraintInfo
import TypeGraphHeuristics (heuristics)
import Types
import Utils (internalError)
import Data.FiniteMap

instance TypeGraphConstraintInfo info => IsTypeGraph (TypeGraph info) info where

   addVertex i info =
      debugTrace ("addVertex " ++ show i) >>
      do createNewGroup (insertVertex i info emptyGroup)
     
   -- add an edge and propagate equality
   addEdge edge@(EdgeID v1 v2) info =
      debugTrace ("addEdge " ++ show edge) >>      
      do propagateEquality [v1,v2]
         combineClasses v1 v2
         updateEquivalenceGroupOf v1 (insertEdge edge info)
         paths <- infinitePaths v1 
         mapM_ (signalInconsistency InfiniteType . fst) (concat paths)
         signalInconsistency InfiniteType v1 -- ?? see TypeBug7

   addClique clique@(cnr,lists) = 
      debugTrace ("addClique " ++ show clique) >>
      do case filter (not . null) lists of
           []                -> return ()
           ((v1,_):_) : rest -> 
              do mapM_ (combineClasses v1) (map (fst . head) rest)
                 updateEquivalenceGroupOf v1 (combineCliques clique)

   verticesInGroupOf i =
      debugTrace ("verticesInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (vertices eqc)

   constantsInGroupOf i =
      debugTrace ("constantsInGroupOf " ++ show i) >>
      do eqc <- equivalenceGroupOf i
         return (constants eqc)         
                       
   {- bug fix 29 november: a history of visited equivalence groups should be recorded because unfolding an implied edge
      might result in a second visit of the same equivalence group, which then might result in unfolding the same implied 
      edge over and over again.  
      5 december: Actually, a second visit of the same equivalence group should not be a problem at all, and should even 
      be allowed. Only the unfolding of an implied edge that has already been unfolded before should be forbidden! 
      10 february: ...and if you encounter an implied edge that has already been unfolded, then you 
      should return a single empty path (which is [[]]), and not the empty list (which is no path 
      at all)!
      -}  
   allPathsList v1 vs = 
      debugTrace ("allPathsList "++show v1++" "++show vs) >>
      do eqc <- equivalenceGroupOf v1
         ps <- rec 20 [] (pathsFrom v1 vs eqc)
         return ps where 
   
      rec i history [] = return []
      rec i history (path:paths)
         | i <= 0   = return []
         | otherwise = do (pathResult,_) <- foldM op ([[]],i) path
                          restResult     <- rec (i - length pathResult) history paths
                          return (pathResult ++ restResult)

             where op (list,i) tuple@(EdgeID v1 v2,edgeInfo) = 
                      case edgeInfo of
                         Implied cnr p1 p2 -> do eqc <- equivalenceGroupOf p1                                                 
                                                 parentspaths <- if (p1,p2) `elem` history
                                                                   then return [[]]
                                                                   else rec i ((p1,p2):history) (pathsFrom p1 [p2] eqc)     
                                                 let f path = [(EdgeID p1 v1,Child cnr)] 
                                                           ++ path 
                                                           ++ [(EdgeID p2 v2,Child cnr)]
                                                 return (take i [ path ++ path' | path <- list, path' <- map f parentspaths ],ceiling (fromIntegral i / fromIntegral (length parentspaths)) :: Int)
                         _                 -> return ([ path ++ [tuple] | path <- list ],i)
             
   deleteEdge edge@(EdgeID v1 v2) =
      debugTrace ("deleteEdge "++show edge) >>
      do eqgroup <- equivalenceGroupOf v1
         removeGroup eqgroup
         let newGroups = splitGroup (removeEdge edge eqgroup)
         mapM_ createNewGroup newGroups
         let is = map representative newGroups
         cliques <- lookForCliques is                   
         mapM_ deleteClique cliques         
         mapM_ checkConsistencyForGroupOf is

   deleteClique clique =
      debugTrace ("deleteClique " ++ show clique) >>
      do let vid = fst . head . head . snd $ clique 
         eqgroup <- equivalenceGroupOf vid
         removeGroup eqgroup
         let newGroups = splitGroup (removeClique clique eqgroup)
         mapM_ createNewGroup newGroups
         let is = map representative newGroups
         cliques <- lookForCliques is
         mapM_ deleteClique cliques
         mapM_ checkConsistencyForGroupOf is
                        
   applyHeuristics = 
      debugTrace "applyHeuristics" >> 
      do (edges, errors) <- heuristics
         mapM_ deleteEdge edges
         mapM_ addError errors                                                                
         addDebug . putStrLn . unlines $ 
            [ "The following edges are selected by the heuristics:"
            , "   " ++ show edges
            ]
                
   
   getConflicts = 
      debugTrace "getConflicts" >>
      let predicate (unificationerror,i) = 
             case unificationerror of
                InfiniteType  -> infinitePaths i      >>= ( return . not . null       )
                ConstantClash -> equivalenceGroupOf i >>= ( return . not . consistent )
                                 
          getRepresentative (unificationerror,i) = 
             do eqc <- equivalenceGroupOf i 
                return (unificationerror,representative eqc)
                                 
      in do signaled <- getSignaledErrors                
            list     <- filterM predicate signaled
            list'    <- mapM getRepresentative list
            let result = nub list'
            setSignaledErrors result
            return result
