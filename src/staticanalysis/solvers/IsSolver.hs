module IsSolver where

import Constraints
import SolveState
import Types
import ConstraintInfo

class (ConstraintInfo info, Monad m) => IsSolver m info | m -> info where
   initialize        ::                     m ()
   makeConsistent    ::                     m ()
   unifyTerms        :: info -> Tp -> Tp -> m ()
   newVariables      :: [Int] ->            m ()
   findSubstForVar   :: Int ->              m Tp
   
   initialize     = return ()    -- default definition (do nothing)
   makeConsistent = return ()    -- default definition (do nothing)
   newVariables _ = return ()    -- default definition (do nothing)   

solveConstraints :: ( IsSolver m info
                    , MonadState (SolveState m info ext) m
                    , Show ext
                    ) => Int -> Constraints m -> m ()
solveConstraints unique constraints = 
   do setUnique unique      
      pushConstraints constraints
      initialize      
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

getReducedPredicates :: (IsSolver m info, MonadState (SolveState m info ext) m) => m Predicates
getReducedPredicates =
   do synonyms    <- getTypeSynonyms
      predicates  <- getPredicates
      substituted <- applySubstGeneral predicates
      let (reduced, errors) = contextReduction synonyms standardClasses substituted
      unless (null errors) $ 
         error (unlines ("" : "Reduction error(s)" : map show errors))
      setPredicates reduced
      return reduced
