module SolveSimple (Simple, evalSimple, solveSimple) where

import FixpointSolveState
import Types
import Constraints
import SolveState
import IsSolver
import Maybe (fromJust)
import ConstraintInfo

type Simple info = Fix info FiniteMapSubstitution {- hack -} Maybe

evalSimple :: Simple info result -> result
evalSimple x = fst . fromJust . runFix x . extend $ emptySubst  
 
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
      predicates  <- getReducedPredicates
      debug       <- getDebug
      let subst = FixpointSubstitution (getWith id s)
      return (uniqueAtEnd, subst, predicates, errors, putStrLn debug)
 
instance Show FiniteMapSubstitution where
   show _ = "<FiniteMapSubstitution>"
   
instance ConstraintInfo info => IsSolver (Simple info) info where
   
   findSubstForVar i = 
      do s <- get
         let sub = getWith id s
         return (lookupInt i sub)
         
   unifyTerms info t1 t2 =
       do synonyms <- getTypeSynonyms 
          t1'      <- applySubst t1
          t2'      <- applySubst t2
          case mguWithTypeSynonyms synonyms t1' t2' of
              Right (used,sub) -> 
                  modify (liftFunction (sub @@))
              Left _ -> addError info
