-- similar to the semantics for type constraints, except that
-- defaulting is applied before generalization of kinds.  

module KindConstraintSemantics where

import Constraints
import TypeConstraints
import IsSolver
import SolveState
import Types
import ConstraintInfo
import Utils (internalError)

instance ( IsSolver m info
         , MonadState (SolveState m info a) m
         , Show info
         ) => SolvableConstraint (TypeConstraint info) m where

   solveConstraint constraint = 
      case constraint of
      
         Equality info t1 t2 ->
            do unifyTerms info t1 t2   
            
         ExplicitInstance info tp ts ->  
            do unique <- getUnique
               let (unique',predicates,its) = instantiate unique ts
                   info' (tp,its) = setOriginalTypeScheme ts (info (its,tp))
               setUnique unique'              
               pushConstraint  (liftConstraint (tp .==. its $ info'))
               let cs = map (PredicateConstraint (info' (tp,its))) predicates
               pushConstraints (liftConstraints cs)

         ImplicitInstance info t1 ms t2 ->         
            do makeConsistent
               t2' <- applySubst t2
               ms' <- mapM applySubst ms
               ps  <- getPredicates
               let scheme = generalize (ftv ms') (map fst ps) (defaultToStar t2')
               pushConstraint (liftConstraint (t1 .::. scheme $ info)) 

         _ -> internalError "KindConstraintSemantics" "instance" "unknown kind constraint"
