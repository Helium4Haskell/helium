module IsSolver where

import Constraints
import SolveState
import Types
import ConstraintInfo

class (ConstraintInfo info, Monad m) => IsSolver m info | m -> info where
   makeConsistent    ::                     m ()
   unifyTerms        :: info -> Tp -> Tp -> m ()
   findSubstForVar   :: Int ->              m Tp
   
   makeConsistent = return ()    -- default definition (do nothing)  

solveConstraints :: ( IsSolver m info
                    , MonadState (SolveState m info ext) m
                    , Show ext
                    ) => Int -> Constraints m -> m ()
solveConstraints unique constraints = 
   do setUnique unique      
      pushConstraints constraints
      stateDebug
      startSolving
      makeConsistent
      
applySubst :: IsSolver m info => Tp -> m Tp
applySubst (TVar i)     = findSubstForVar i
applySubst tp@(TCon _)  = return tp
applySubst (TApp t1 t2) = do t1' <- applySubst t1
                             t2' <- applySubst t2
                             return (TApp t1' t2')
                             
applySubstGeneral :: (Substitutable a, IsSolver m info) => a -> m a
applySubstGeneral scheme = 
   do let var = ftv scheme
      tps <- mapM findSubstForVar var
      let sub = listToSubstitution (zip var tps)                          
      return (sub |-> scheme)   

reducePredicates :: (IsSolver m info, MonadState (SolveState m info ext) m) => m ()
reducePredicates = 
   do synonyms    <- getTypeSynonyms
      predicates  <- getPredicates
      substituted <- let f (predicate, info) = 
                              do predicate' <- applySubstGeneral predicate
                                 return (predicate', info)
                     in mapM f predicates
      let (reduced, errors) = associatedContextReduction synonyms standardClasses substituted
      mapM_ addError [ setReductionError p info | ReductionError (p, info) <- errors ]
      setPredicates reduced
