module TypeConstraintSemantics where

import Constraints
import TypeConstraints
import IsSolver
import SolveState
import SolverOptions
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
               -- mapM_ solveOne [ PredConstraint (f2 p) p | p <- predicates ]
               pushConstraint (liftConstraint (tp .==. its $ info'))

         ImplicitInstance info t1 ms t2 ->         
            do makeConsistent
               t2' <- applySubst t2
               ms' <- mapM applySubst ms
               --ps  <- getReducedPredicates
               let scheme = generalize (ftv ms') [] {- (map fst ps) -} t2'
               pushConstraint (liftConstraint (t1 .::. scheme $ info)) 
               
         MakeConsistent ->
            do makeConsistent
            
   checkConstraint constraint =
      case constraint of

         Equality info t1 t2 ->
            do opt <- getSolverOptions
               t1' <- applySubst t1
               t2' <- applySubst t2
               let synonyms = snd (getTypeSynonyms opt)
               return (expandType synonyms t1' == expandType synonyms t2')   
                    
         ExplicitInstance info tp ts ->   
            do tp' <- applySubst tp
               ts' <- applySubstScheme ts
               return (isInstanceOf tp' ts')                        
               
         ImplicitInstance info t1 ms t2 ->     
            do t1' <- applySubst t1
               ms' <- mapM applySubst ms
               t2' <- applySubst t2
               let scheme = generalize (ftv ms') [] {- (map fst ps) -} t2'
               return (isInstanceOf t1' scheme)                            
         
isInstanceOf :: Tp -> TpScheme -> Bool
isInstanceOf tp ts = True -- !!!!!!!!!!!! undefined
