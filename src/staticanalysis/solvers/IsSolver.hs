module IsSolver where

import Constraints
import SolveState
import Types
import SolverOptions
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
                    ) => (m result -> result) -> Int -> SolverOptions -> Constraints m -> m result -> result
solveConstraints evaluator unique options constraints monad = evaluator $
   do setUnique unique    
      setSolverOptions options
      initialize
      pushConstraints constraints
      stateDebug
      startSolving
      makeConsistent
      monad     
      
applySubst :: IsSolver m info => Tp -> m Tp
applySubst (TVar i)     = findSubstForVar i
applySubst tp@(TCon _)  = return tp
applySubst (TApp t1 t2) = do t1' <- applySubst t1
                             t2' <- applySubst t2
                             return (TApp t1' t2')
                             
applySubstScheme :: IsSolver m info => TpScheme -> m TpScheme
applySubstScheme scheme = 
   do let var = ftv scheme
      tps <- mapM findSubstForVar var
      let sub = listToSubstitution (zip var tps)                          
      return (sub |-> scheme)   
