-----------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveTypeGraph.hs : Solve a set of type constraints using a type graph.
--   All instances of the class TypeGraph are also an instance of the class
--   ConstraintSolver. Known instance of the class TypeGraph is the data
--   type EquivalenceGroups.
--
------------------------------------------------------------------------------

module SolveTypeGraph where

import ST
import EquivalenceGroup
import Types
import FixpointSolveState
import IsSolver
import IsTypeGraph
import Constraints
import SolveState
import List
import Utils (internalError, doubleSizeOfSTArray)
   
type TypeGraph info = Fix info () (STMonad (TG info))

data TG info state = 
        TG { indexSTArray   :: STArray state Int (STRef state (EquivalenceGroup info))
           , signaledErrors :: STRef state [(UnificationError,Int)]
           }  

evalTypeGraph :: TypeGraph info result -> result
evalTypeGraph x = fst $ runSTMonad $ runFix x newState

solveTypeGraph :: IsTypeGraph (TypeGraph info) info => SolverOptions -> Constraints (TypeGraph info) -> TypeGraph info result -> result
solveTypeGraph = solveConstraints evalTypeGraph

buildSubstitutionTypeGraph :: IsTypeGraph (TypeGraph info) info => TypeGraph info WrappedSubstitution 
buildSubstitutionTypeGraph = do newUnique <- getUnique
                                bintreesubst <- rec (0, newUnique - 1)
                                return (wrapSubstitution bintreesubst)
  where
    rec (a,b) 
      | a == b    = do tp <- findSubstForVar a
                       return (BinTreeSubstNode tp)
      | a < b     = do let split = (a+b) `div` 2
                       left  <- rec (a,split)
                       right <- rec (split+1,b)
                       return (BinTreeSubstSplit split left right)    
      | otherwise = do return BinTreeSubstEmpty
     
-----------------------------------------------------------------------------------

instance IsTypeGraph (TypeGraph info) info => IsSolver (TypeGraph info) info where

   initialize =
      do unique <- getUnique
         initializeTypeGraph
         newVariables [0..unique-1]

   unifyTerms info t1 t2 =
      do v1 <- makeTermGraph t1
         v2 <- makeTermGraph t2      
         propagateEquality [v1,v2]    
         addEdge (EdgeID v1 v2) (Initial info)

   makeConsistent =
      do consistent <- isConsistent
         if consistent 
           then 
             checkErrors
           else 
             do (edges, errors) <- getHeuristics                         
                mapM_ addError errors               
                mapM_ deleteEdge edges                        
                addDebug $ "> removed edges "++show edges
                makeConsistent

   newVariables is = 
      mapM_ (\i -> addVertexWithChildren i (Nothing,[],Nothing)) is

   findSubstForVar i =   
      do synonyms  <- getTypeSynonyms
         vertices  <- getVerticesInGroup i
         let constants = nubBy (\x y -> fst x == fst y)
                       $ [ original | (_,(_,_,Just original)) <- vertices ]
                      ++ [ (s,cs)   | (_,(Just s,cs,Nothing)) <- vertices ] 
         types <- let f (s,cs) = do ts <- mapM findSubstForVar cs
                                    return (foldl TApp (TCon s) ts)
                  in mapM f constants  
         case types of
           []     -> return (TVar . fst . head $ vertices)
           (t:ts) -> let op t1 t2 = case mguWithTypeSynonyms synonyms t1 t2 of
                                      Left _      -> internalError "SolveTypeGraph.hs" "findSubstForVar" "multiple constants present"
                                      Right (b,s) -> equalUnderTypeSynonyms synonyms (s |-> t1) (s |-> t2)
                     in return (foldr op t ts)

equivalenceGroupOf :: Int -> TG info state -> ST state (EquivalenceGroup info)
equivalenceGroupOf i groups = equivalenceGroupRefOf i groups >>= readSTRef
     
equivalenceGroupRefOf :: Int -> TG info state -> ST state (STRef state (EquivalenceGroup info))
equivalenceGroupRefOf i groups = readSTArray (indexSTArray groups) i 

updateEquivalenceGroupOf :: Int -> (EquivalenceGroup info -> EquivalenceGroup info) -> TG info state -> ST state ()
updateEquivalenceGroupOf i f groups = do ref <- equivalenceGroupRefOf i groups
                                         myModifySTRef ref f

signalInconsistency :: UnificationError -> Int -> TypeGraph info ()
signalInconsistency u i = liftUse ( flip myModifySTRef ((u,i):) . signaledErrors )

myModifySTRef :: STRef state a -> (a -> a) -> ST state ()  -- see also GHC library
myModifySTRef ref f = do a <- readSTRef ref
                         writeSTRef ref (f a)
   
combineClasses :: IsTypeGraph (TypeGraph info) info => Int -> Int -> TypeGraph info ()
combineClasses v1 v2 =
   do liftUse
        (\groups -> do ref1 <- equivalenceGroupRefOf v1 groups
                       ref2 <- equivalenceGroupRefOf v2 groups
                       unless (ref1 == ref2) $
                         do eqc1 <- readSTRef ref1
                            eqc2 <- readSTRef ref2
                            let changeRef (i,_) = writeSTArray (indexSTArray groups) i ref1
                            mapM_ changeRef (vertices eqc2) 
                            writeSTRef ref1 (combineGroups eqc1 eqc2))
                            
      checkConsistencyForGroupOf v1

checkConsistencyForGroupOf :: IsTypeGraph (TypeGraph info) info => Int -> TypeGraph info ()
checkConsistencyForGroupOf i = 
   do strings <- getConstantsInGroup i
      when (length strings > 1) (signalInconsistency ConstantClash i)

removeImpliedClique :: IsTypeGraph (TypeGraph info) info => Cliques -> TypeGraph info ()
removeImpliedClique clique =
   do is <- liftUse
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
  
testArrayBounds :: Int -> TypeGraph info ()
testArrayBounds i = 
   do guard <- liftUse ( return . (i>) . snd . boundsSTArray . indexSTArray )
      when guard $  

         do addDebug "size of state array is doubled"
            liftUpdate 
               (\groups -> 
                  do let err = internalError "SolveEquivalenceGroups.hs" 
                                             "testArrayBounds" 
                                             "resize starray is not initialized"
                     newarray <- doubleSizeOfSTArray err (indexSTArray groups)
                     return (groups { indexSTArray = newarray }))
