module SolveSimple (Simple, evalSimple, solveSimple) where

import Types
import Constraints
import SolveState
import IsSolver
import FixpointSolveState
import ConstraintInfo

type Simple info = Fix info FiniteMapSubstitution

evalSimple :: Simple info result -> result
evalSimple x = fst . runFix x . extend $ emptySubst  
 
solveSimple :: ( ConstraintInfo info
               , SolvableConstraint constraint (Simple info)
               , Show constraint
               ) => OrderedTypeSynonyms -> Int -> [constraint]  
                 -> (Int, FixpointSubstitution, Predicates, [info], IO ())
solveSimple synonyms unique constraints =
   evalSimple $
   do setTypeSynonyms synonyms
      solveConstraints unique (liftConstraints constraints)
      uniqueAtEnd <- getUnique
      errors      <- getErrors
      s           <- get      
      predicates  <- getPredicates
      debug       <- getDebug
      let subst = FixpointSubstitution (getWith id s)
      return (uniqueAtEnd, subst, map fst predicates, errors, debug)
 
instance Show FiniteMapSubstitution where
   show _ = "<FiniteMapSubstitution>"
   
instance ConstraintInfo info => IsSolver (Simple info) info where
   
   findSubstForVar i = 
      do s <- get
         let sub = getWith id s
         return (lookupInt i sub)
         
   unifyTerms info t1 t2 =
       do synonyms <- getTypeSynonyms
          addError info 
          t1'      <- applySubst t1
          t2'      <- applySubst t2
          case mguWithTypeSynonyms synonyms t1' t2' of
              Right (used,sub) -> 
                  modify (liftFunction (sub @@))
              Left _ -> addError info

   makeConsistent = 
      do reducePredicates
