module TypeConstraintSemantics where

import Constraints
import TypeConstraints
import IsSolver
import SolveState
import Types
import ConstraintInfo

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
               newVariables [unique..unique'-1]               
               pushConstraint  (liftConstraint (tp .==. its $ info'))
               let cs = map PredicateConstraint predicates
               pushConstraints (liftConstraints cs)

         ImplicitInstance info t1 ms t2 ->         
            do makeConsistent
               t2' <- applySubst t2
               ms' <- mapM applySubst ms
               ps  <- getReducedPredicates
               let scheme = generalize (ftv ms') ps t2'
               pushConstraint (liftConstraint (t1 .::. scheme $ info)) 
               
         MakeConsistent ->
            do makeConsistent
            
         PredicateConstraint p ->
            do addPredicate p
            
   checkConstraint constraint =
      case constraint of

         Equality info t1 t2 ->
            do synonyms <- getTypeSynonyms
               t1' <- applySubst t1
               t2' <- applySubst t2               
               return (expandType (snd synonyms) t1' == expandType (snd synonyms) t2')   
                    
         ExplicitInstance info tp ts ->   
            do tp' <- applySubst tp
               ts' <- applySubstGeneral ts
               return (isInstanceOf tp' ts')                        
               
         ImplicitInstance info t1 ms t2 ->     
            do t1' <- applySubst t1
               ms' <- mapM applySubst ms
               t2' <- applySubst t2
               ps  <- getReducedPredicates
               let scheme = generalize (ftv ms') [] t2'
               return (isInstanceOf t1' scheme)                            
         
isInstanceOf :: Tp -> TpScheme -> Bool
isInstanceOf tp ts = True -- !!!!!!!!!!!! undefined
