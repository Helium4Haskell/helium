-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- EquivalenceGroupsImplementation.hs : The implementation that an equivalence 
--    group is an instance of a type graph.
--
-- Note: nothing is exported from this module, except for the instance
--    declaration.
--
------------------------------------------------------------------------------

module EquivalenceGroupsImplementation () where

import SolveTypeGraph
import SolveEquivalenceGroups
import EquivalenceGroup
import SolveState
import ST
import TypeGraphConstraintInfo   ( TypeGraphConstraintInfo )
import TypeGraphHeuristics  ( heuristics              )
import Types                ( UnificationError(..)    )
import Utils                ( internalError           )
import Monad                ( foldM, filterM, unless  )
import List                 ( nub                     )
import Int 
import Monad
import ConstraintInfo 

instance TypeGraphConstraintInfo info => TypeGraph EquivalenceGroups info where

   initializeTypeGraph =
      do unique <- getUnique
         setSolver
           (do starray     <- newSTArray (0,4*unique) (internalError "EquivalenceGroupsImplementation.hs" "initializeTypeGraph" "not initialized")
               errorgroups <- newSTRef []
               return (EQGroups starray errorgroups))

   addVertex = internalError "EquivalenceGroupsImplementation.hs" "addVertex" "this function should not be called"

   addVertexWithChildren i info =
      do testArrayBounds i
         useSolver
           (\groups -> do ref <- newSTRef (insertVertex i info emptyGroup)
                          writeSTArray (indexSTArray groups) i ref)
          
   -- be carefull: the equality is not automatically propagated!
   addEdge (EdgeID v1 v2) edgeinfo =
      case edgeinfo of
         Initial info -> do combineClasses v1 v2
                            useSolver
                               (updateEquivalenceGroupOf v1 (insertEdge (EdgeID v1 v2) info))
                            paths <- infinitePaths v1 
                            mapM_ (signalInconsistency InfiniteType . fst) (concat paths)
                            signalInconsistency InfiniteType v1
         _            -> internalError "EquivalenceGroupsImplementation.hs" "addEdge" "should not be called with this kind of edge"

   addImpliedClique (cnr,lists) =      
      case filter (not . null) lists of
        []                -> return ()
        ((v1,_):_) : rest -> do mapM_ (combineClasses v1) (map (fst . head) rest)
                                useSolver
                                   (updateEquivalenceGroupOf v1 (combineCliques (cnr,lists)))

   getVerticesInGroup i =
      useSolver
         (\groups -> do eqc <- equivalenceGroupOf i groups
                        return (vertices eqc))

   getChildrenInGroup i =
      useSolver
         (\groups -> do eqc <- equivalenceGroupOf i groups
                        return [ (i,children) | (i,(_,children,_)) <- vertices eqc, not (null children) ])

   getConstantsInGroup i =
         useSolver
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
   getPathsFrom v1 vs = do ps <- useSolver  
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
                                                 return (take i [ path ++ path' | path <- list, path' <- map f parentspaths ],ceiling (fromInt i / fromInt (length parentspaths)) :: Int)
                         _                 -> return ([ path ++ [tuple] | path <- list ],i)
   
   -- check all the signaled errors whether they are still inconsistent.       
   getConflicts =
      do let predicate (unificationerror,i) = 
                case unificationerror of
                   InfiniteType  -> infinitePaths i       >>= ( return . not  . null   )
                   ConstantClash -> getConstantsInGroup i >>= ( return . (>1) . length )
                                       
             getRepresentative (unificationerror,i) = 
                useSolver (\groups -> do eqc <- equivalenceGroupOf i groups
                                         return (unificationerror,representative eqc))
                                       
         signaled <- useSolver ( readSTRef . signaledErrors )                                            
         list     <- filterM predicate signaled
         list'    <- mapM getRepresentative list

         let conflicts = nub list'
         useSolver ( flip writeSTRef conflicts . signaledErrors )         
         return conflicts

   deleteEdge (EdgeID v1 v2) =
      do is <- useSolver
            (\groups -> do eqgroup <- equivalenceGroupOf v1 groups
                           
                           let makeRef eqc = do ref <- newSTRef eqc
                                                let changeRef (i,_) = writeSTArray (indexSTArray groups) i ref
                                                mapM_ changeRef (vertices eqc)
                                                return (representative eqc)
                                                
                           mapM makeRef . splitGroup . removeEdge (EdgeID v1 v2) $ eqgroup)
         cliques <- lookForCliques is                   
         mapM_ removeImpliedClique cliques         
         mapM_ checkConsistencyForGroupOf is
         
   getHeuristics = heuristics
