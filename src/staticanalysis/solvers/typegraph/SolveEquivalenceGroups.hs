-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveEquivalenceGroups.hs : Solve a set of type constraints using equivalence
--    groups. See EquivalenceGroupsImplementation for an instance declaration
--    of the class TypeGraph.
--
------------------------------------------------------------------------------

module SolveEquivalenceGroups where

import EquivalenceGroup
import Types
import SolveConstraints
import SolveTypeGraph
import ST
import Monad               ( unless, when                       )
import Utils               ( internalError, doubleSizeOfSTArray )
import ConstraintInfo      ( ConstraintInfo(..) ) 
import TypeGraphConstraintInfo ( TypeGraphConstraintInfo(..) )
-- import EquivalenceGroupsToHTML ( equivalenceGroupsToHTML )

data EquivalenceGroups info state = 
        EQGroups { indexSTArray   :: STArray state Int (STRef state (EquivalenceGroup info))
                 , signaledErrors :: STRef state [(UnificationError,Int)]
                 }          

equivalenceGroupOf :: Int -> EquivalenceGroups info state -> ST state (EquivalenceGroup info)
equivalenceGroupOf i groups = equivalenceGroupRefOf i groups >>= readSTRef

equivalenceGroupRefOf :: Int -> EquivalenceGroups info state -> ST state (STRef state (EquivalenceGroup info))
equivalenceGroupRefOf i groups = readSTArray (indexSTArray groups) i 

updateEquivalenceGroupOf :: Int -> (EquivalenceGroup info -> EquivalenceGroup info) -> EquivalenceGroups info state -> ST state ()
updateEquivalenceGroupOf i f groups = do ref <- equivalenceGroupRefOf i groups
                                         myModifySTRef ref f

signalInconsistency :: UnificationError -> Int -> SolveState EquivalenceGroups info ()
signalInconsistency u i = useSolver ( flip myModifySTRef ((u,i):) . signaledErrors )

myModifySTRef :: STRef state a -> (a -> a) -> ST state ()  -- see also GHC library
myModifySTRef ref f = do a <- readSTRef ref
                         writeSTRef ref (f a)
           
combineClasses :: (TypeGraph EquivalenceGroups info,ConstraintInfo info) => Int -> Int -> SolveState EquivalenceGroups info ()
combineClasses v1 v2 =
   do useSolver
        (\groups -> do ref1 <- equivalenceGroupRefOf v1 groups
                       ref2 <- equivalenceGroupRefOf v2 groups
                       unless (ref1 == ref2) $
                         do eqc1 <- readSTRef ref1
                            eqc2 <- readSTRef ref2
                            let changeRef (i,_) = writeSTArray (indexSTArray groups) i ref1
                            mapM_ changeRef (vertices eqc2) 
                            writeSTRef ref1 (combineGroups eqc1 eqc2))
                            
      checkConsistencyForGroupOf v1


checkConsistencyForGroupOf :: (TypeGraph EquivalenceGroups info,ConstraintInfo info) => Int -> SolveState EquivalenceGroups info ()
checkConsistencyForGroupOf i = 
   do strings <- getConstantsInGroup i
      when (length strings > 1) (signalInconsistency ConstantClash i)

removeImpliedClique :: (TypeGraph EquivalenceGroups info,ConstraintInfo info) => Cliques -> SolveState EquivalenceGroups info ()
removeImpliedClique clique =
   do is <- useSolver
         (\groups -> do let vid = fst . head . head . snd $ clique
                        eqgroup <- equivalenceGroupOf vid groups
                        let makeRef eqc = do ref <- newSTRef eqc
                                             let changeRef (i,_) = writeSTArray (indexSTArray groups) i ref
                                             mapM_ changeRef (vertices eqc)
                                             return (representative eqc)
                                             
                        mapM makeRef . splitGroup . removeClique clique $ eqgroup)                     
      cliques <- lookForCliques is
      mapM_ removeImpliedClique cliques
      mapM_ checkConsistencyForGroupOf is

testArrayBounds :: Int -> SolveState EquivalenceGroups info ()
testArrayBounds i = 
   do guard <- useSolver ( return . (i>) . snd . boundsSTArray . indexSTArray ) 
      when guard $  

         do addDebug (putStrLn "size of state array is doubled")
            updateSolver 
               (\groups -> 
                  do let err = internalError "SolveEquivalenceGroups.hs" 
                                             "testArrayBounds" 
                                             "resize starray is not initialized"
                     newarray <- doubleSizeOfSTArray err (indexSTArray groups)
                     return (groups { indexSTArray = newarray }))

{- misc utility function -} 
{-
representativesOfAllParents :: Int -> SolveState EquivalenceGroups info [Int]
representativesOfAllParents i = useSolver (rec [i] []) where

   rec []     result groups = return result
   rec (i:is) result groups = do eqc <- equivalenceGroupOf i groups
                                 let representative = fst (head (vertices eqc))
                                 if representative `elem` result 
                                    then rec is result groups
                                    else let ps = [ i | (_,(_,i):_) <- cliques eqc ]
                                         in rec (ps++is) (representative:result) groups    
-- Note that the domain of the substitution that is returned ONLY contains
-- the type variables that are also present in the (initial) constraint set.
-- This makes the final substitution smaller, and therefore more efficient.

-}
                              
solveEquivalenceGroups :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => RunnableSolver info
solveEquivalenceGroups unique = runSolver buildSubstitution unique where

   buildSubstitution :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => SolveState EquivalenceGroups info WrappedSubstitution 
   buildSubstitution = do -- equivalenceGroupsToHTML
                          newUnique <- getUnique
                          bintreesubst <- rec (0, newUnique - 1)
                          return (wrapSubstitution bintreesubst)
   
   rec (a,b) 
     | a == b    = do tp <- findSubstForVar a
                      return (BinTreeSubstNode tp)
     | a < b     = do let split = (a+b) `div` 2
                      left  <- rec (a,split)
                      right <- rec (split+1,b)
                      return (BinTreeSubstSplit split left right)    
     | otherwise = do return BinTreeSubstEmpty       
     

 
