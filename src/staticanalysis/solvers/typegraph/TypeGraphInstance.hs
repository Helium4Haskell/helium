module TypeGraphInstance where

import EquivalenceGroup
import FixpointSolveState
import IsTypeGraph
import List
import ST
import SolveState
import SolveTypeGraph
import TypeGraphConstraintInfo
import TypeGraphHeuristics (heuristics)
import Types
import Utils (internalError)
import FiniteMap

instance TypeGraphConstraintInfo info => IsTypeGraph (TypeGraph info) info where
   initializeTypeGraph =
      do unique <- getUnique
         liftSet
           (do starray     <- newSTRef emptyFM
               errorgroups <- newSTRef []
               return (TG starray errorgroups))

   addVertexWithChildren i info =
      liftUse
        (\groups -> do fm  <- readSTRef (finiteMapRef groups)
                       ref <- newSTRef (insertVertex i info emptyGroup)
                       writeSTRef (finiteMapRef groups) (addToFM fm i ref))
     
   -- be carefull: the equality is not automatically propagated!
   addEdge (EdgeID v1 v2) edgeinfo =
      case edgeinfo of
         Initial info -> do combineClasses v1 v2
                            liftUse
                               (updateEquivalenceGroupOf v1 (insertEdge (EdgeID v1 v2) info))
                            paths <- infinitePaths v1 
                            mapM_ (signalInconsistency InfiniteType . fst) (concat paths)
                            signalInconsistency InfiniteType v1
         _            -> internalError "EquivalenceGroupsImplementation.hs" "addEdge" "should not be called with this kind of edge"

   addImpliedClique (cnr,lists) =      
      case filter (not . null) lists of
        []                -> return ()
        ((v1,_):_) : rest -> do mapM_ (combineClasses v1) (map (fst . head) rest)
                                liftUse
                                   (updateEquivalenceGroupOf v1 (combineCliques (cnr,lists)))

   getVerticesInGroup i =
      liftUse
         (\groups -> do eqc <- equivalenceGroupOf i groups
                        return (vertices eqc))

   getChildrenInGroup i =
      liftUse
         (\groups -> do eqc <- equivalenceGroupOf i groups
                        return [ (i,children) | (i,(_,children,_)) <- vertices eqc, not (null children) ])
   
   getConstantsInGroup i =
      liftUse
         (\groups -> do eqc <- equivalenceGroupOf i groups
                        return (constants eqc))                        

   {- bug fix 29 november: a history of visited equivalence groups should be recorded because unfolding an implied edge
      might result in a second visit of the same equivalence group, which then might result in unfolding the same implied 
      edge over and over again.  
      5 december: Actually, a second visit of the same equivalence group should not be a problem at all, and should even 
      be allowed. Only the unfolding of an implied edge that has already been unfolded before should be forbidden! 
      10 february: ...and if you encounter an implied edge that has already been unfolded, then you 
      should return a single empty path (which is [[]]), and not the empty list (which is no path 
      at all)!
      -}  
   getPathsFrom v1 vs = do ps <- liftUse  
                                    (\groups -> do eqc <- equivalenceGroupOf v1 groups
                                                   rec 20 [] (pathsFrom v1 vs eqc) groups) 
                           return ps where 
   
      rec i history [] groups = return []
      rec i history (path:paths) groups
         | i <= 0   = return []
         | otherwise = do (pathResult,_) <- foldM op ([[]],i) path
                          restResult     <- rec (i - length pathResult) history paths groups
                          return (pathResult ++ restResult)

             where op (list,i) tuple@(EdgeID v1 v2,edgeInfo) = 
                      case edgeInfo of
                         Implied cnr p1 p2 -> do eqc <- equivalenceGroupOf p1 groups                                                 
                                                 parentspaths <- if (p1,p2) `elem` history
                                                                   then return [[]]
                                                                   else rec i ((p1,p2):history) (pathsFrom p1 [p2] eqc) groups     
                                                 let f path = [(EdgeID p1 v1,Child cnr)] 
                                                           ++ path 
                                                           ++ [(EdgeID p2 v2,Child cnr)]
                                                 return (take i [ path ++ path' | path <- list, path' <- map f parentspaths ],ceiling (fromIntegral i / fromIntegral (length parentspaths)) :: Int)
                         _                 -> return ([ path ++ [tuple] | path <- list ],i)
     
   -- check all the signaled errors whether they are still inconsistent.       
   getConflicts =
      do let predicate (unificationerror,i) = 
                case unificationerror of
                   InfiniteType  -> infinitePaths i       >>= ( return . not  . null   )
                   ConstantClash -> getConstantsInGroup i >>= ( return . (>1) . length )
                                       
             getRepresentative (unificationerror,i) = 
                liftUse (\groups -> do eqc <- equivalenceGroupOf i groups
                                       return (unificationerror,representative eqc))
                                       
         signaled <- liftUse ( readSTRef . signaledErrors )                                            
         list     <- filterM predicate signaled
         list'    <- mapM getRepresentative list

         let conflicts = nub list'
         liftUse ( flip writeSTRef conflicts . signaledErrors )         
         return conflicts
         
   deleteEdge (EdgeID v1 v2) =
      do is <- liftUse
            (\groups -> do eqgroup <- equivalenceGroupOf v1 groups
                           
                           let makeRef eqc = do fm  <- readSTRef (finiteMapRef groups)   
                                                ref <- newSTRef eqc
                                                let fm' = addListToFM fm [ (i,ref) | (i,_) <- vertices eqc ]
                                                writeSTRef (finiteMapRef groups) fm'
                                                return (representative eqc)
                                                
                           mapM makeRef . splitGroup . removeEdge (EdgeID v1 v2) $ eqgroup)
         cliques <- lookForCliques is                   
         mapM_ removeImpliedClique cliques         
         mapM_ checkConsistencyForGroupOf is
         
   getHeuristics = heuristics
