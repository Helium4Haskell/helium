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

import Control.Monad.ST
import Data.STRef
import EquivalenceGroup
import Types
import FixpointSolveState
import IsSolver
import IsTypeGraph
import Constraints
import SolveState
import List
import Utils (internalError)
import Data.FiniteMap
import Maybe
 
type TypeGraph info   = Fix info (TG info)

data TG info = 
        TG { referenceMap            :: FiniteMap Int Int 
           , equivalenceGroupMap     :: FiniteMap Int (EquivalenceGroup info)
           , equivalenceGroupCounter :: Int
           , signaledErrors          :: [(UnificationError,Int)]
           }

emptyTG :: TG info           
emptyTG = TG { referenceMap            = emptyFM
             , equivalenceGroupMap     = emptyFM
             , equivalenceGroupCounter = 0 
             , signaledErrors          = []
             }
           

evalTypeGraph :: TypeGraph info result -> result
evalTypeGraph x = fst . runFix x . extend $ emptyTG

solveTypeGraph :: ( IsTypeGraph (TypeGraph info) info
                  , SolvableConstraint constraint (TypeGraph info)
                  , Show constraint
                  ) => (OrderedTypeSynonyms, [[(String, TpScheme)]]) -> Int -> [constraint]  
                    -> (Int, FixpointSubstitution, Predicates, [info], IO ())
solveTypeGraph (synonyms, siblings) unique constraints =
   evalTypeGraph $
   do setTypeSynonyms synonyms
      addSiblings siblings
      solveConstraints unique (liftConstraints constraints)
      uniqueAtEnd <- getUnique
      errors      <- getErrors
      subst       <- buildSubstitutionTypeGraph
      predicates  <- getPredicates
      debug       <- getDebug
      return (uniqueAtEnd, subst, map fst predicates, errors, debug)

buildSubstitutionTypeGraph :: IsTypeGraph (TypeGraph info) info => TypeGraph info FixpointSubstitution 
buildSubstitutionTypeGraph =
   do is  <- getFromTG (keysFM . referenceMap)
      tps <- mapM findSubstForVar is
      let notIdentity (i, TVar j) = i /= j
          notIdentity _           = True
      return (FixpointSubstitution $ listToFM $ filter notIdentity $ zip is tps)

getFromTG :: (TG info -> a) -> TypeGraph info a
getFromTG = gets . getWith

updateTG :: (TG info -> TG info) -> TypeGraph info ()
updateTG = modify . liftFunction

instance Show (TG info) where
   show tg = "<type graph>"

-----------------------------------------------------------------------------------

instance IsTypeGraph (TypeGraph info) info => IsSolver (TypeGraph info) info where

   unifyTerms info t1 t2 =
      debugTrace ("unifyTerms "++show t1++" "++show t2) >>
      do v1 <- makeTermGraph t1
         v2 <- makeTermGraph t2     
         addEdge (EdgeID v1 v2) info

   makeConsistent =
      debugTrace "makeConsistent" >>
      do conflicts <- getConflicts
         if (null conflicts) 
           then 
             do reducePredicates
                (checkErrors :: IsTypeGraph (TypeGraph a) a => TypeGraph a ())
           else 
             do applyHeuristics
                makeConsistent

   findSubstForVar i =
      debugTrace ("findSubstForVar " ++ show i) >>
      do synonyms  <- getTypeSynonyms
         eqgroup <- equivalenceGroupOf i
         let constantsList = constants eqgroup
             childrenList  = [ (l, r) | (_, (VApp l r, _)) <- vertices eqgroup]
             originalsList = [ foldl TApp (TCon s) (map TVar is) | (_, (_, Just (s, is))) <- vertices eqgroup ]
             err = internalError "SolveTypeGraph.hs" "findSubstForVar" "inconsistent type graph"
         unless (consistent eqgroup) err
         case originalsList of 
            t:ts -> let op t1 t2 = case mguWithTypeSynonyms synonyms t1 t2 of
                                      Left _      -> internalError "SolveTypeGraph.hs" "findSubstForVar" "inconsistent type graph"
                                      Right (b,s) -> equalUnderTypeSynonyms synonyms (s |-> t1) (s |-> t2)
                    in applySubst (foldr op t ts)
            [] -> case constantsList of 
                     [s] -> return (TCon s)
                     []  -> case childrenList of
                               (l,r):_ -> applySubst (TApp (TVar l) (TVar r))
                               []      -> return (TVar (representative eqgroup))
                     _   -> err                    

-----------------------------------------------------------------------------------

equivalenceGroupOf :: Int -> TypeGraph info (EquivalenceGroup info)
equivalenceGroupOf i =
   do maybeNr <- getFromTG (flip lookupFM i . referenceMap)
      case maybeNr of 
         Nothing ->
            return (insertVertex i (VVar,Nothing) emptyGroup)
         Just eqnr -> 
            let err = internalError "SolveTypeGraph.hs" "equivalenceGroupOf" "error in lookup map"
            in getFromTG (\x -> lookupWithDefaultFM (equivalenceGroupMap x) err eqnr)         

updateEquivalenceGroupOf :: Int -> (EquivalenceGroup info -> EquivalenceGroup info) -> TypeGraph info ()
updateEquivalenceGroupOf i f = 
   do eqgrp <- equivalenceGroupOf i 
      updateTG 
         (\groups -> let err  = internalError "SolveTypeGraph.hs" "updateEquivalenceGroupOf" "error in lookup map"
                         eqnr = lookupWithDefaultFM (referenceMap groups) err i
                     in groups { equivalenceGroupMap = addToFM (equivalenceGroupMap groups) eqnr (f eqgrp) })
  
areInTheSameGroup :: Int -> Int -> TypeGraph info Bool
areInTheSameGroup v1 v2 =
   getFromTG 
      (\groups -> let eqnr1 = lookupFM (referenceMap groups) v1
                      eqnr2 = lookupFM (referenceMap groups) v2
                  in eqnr1 == eqnr2 && isJust eqnr1)

removeGroup :: EquivalenceGroup info -> TypeGraph info ()
removeGroup eqgroup = 
   updateTG
      (\groups -> let vertexIDs  = map fst (vertices eqgroup)
                      oldGroupNr = maybe [] (:[]) (lookupFM (referenceMap groups) (head vertexIDs))
                  in groups { referenceMap        = delListFromFM (referenceMap groups) vertexIDs -- is not necessary
                            , equivalenceGroupMap = delListFromFM (equivalenceGroupMap groups) oldGroupNr
                            })
                                              
createNewGroup :: EquivalenceGroup info -> TypeGraph info ()
createNewGroup eqgroup =
   updateTG
      (\groups -> let newGroupNumber = equivalenceGroupCounter groups
                      list = [(i, newGroupNumber) | (i, _) <- vertices eqgroup]
                  in groups { referenceMap            = addListToFM (referenceMap groups) list
                            , equivalenceGroupMap     = addToFM (equivalenceGroupMap groups) newGroupNumber eqgroup
                            , equivalenceGroupCounter = newGroupNumber + 1
                            })
            
-----------------------------------------------------------------------------------

getSignaledErrors :: TypeGraph info [(UnificationError, Int)]
getSignaledErrors = getFromTG signaledErrors

setSignaledErrors :: [(UnificationError, Int)] -> TypeGraph info ()
setSignaledErrors xs = updateTG (\x -> x { signaledErrors = xs })

signalInconsistency :: UnificationError -> Int -> TypeGraph info ()
signalInconsistency u i = 
   do xs <- getSignaledErrors
      setSignaledErrors ((u, i):xs) 
      
-----------------------------------------------------------------------------------
   
combineClasses :: IsTypeGraph (TypeGraph info) info => Int -> Int -> TypeGraph info ()
combineClasses v1 v2 =
   debugTrace ("combineClasses " ++ show v1 ++ " " ++ show v2) >>
   do condition <- areInTheSameGroup v1 v2
      unless condition $ 
         do eqc1 <- equivalenceGroupOf v1
            eqc2 <- equivalenceGroupOf v2   
            removeGroup eqc1
            removeGroup eqc2
            createNewGroup (combineGroups eqc1 eqc2)  
            checkConsistencyForGroupOf v1

checkConsistencyForGroupOf :: IsTypeGraph (TypeGraph info) info => Int -> TypeGraph info ()
checkConsistencyForGroupOf i = 
   debugTrace ("checkConsistencyForGroupOf " ++ show i) >>
   do eqgroup <- equivalenceGroupOf i
      unless (consistent eqgroup)
         (signalInconsistency ConstantClash i)
