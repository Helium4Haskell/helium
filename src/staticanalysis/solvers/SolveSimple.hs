module SolveSimple (Simple, evalSimple, solveSimple) where

import FixpointSolveState
import Types
import Constraints
import SolveState
import IsSolver
import SolverOptions
import Maybe (fromJust)
import ConstraintInfo

type Simple info = Fix info FiniteMapSubstitution {- hack -} Maybe

evalSimple :: Simple info result -> result
evalSimple x = fst . fromJust . runFix x . extend $ emptySubst
   
solveSimple :: ConstraintInfo info => Int -> SolverOptions -> Constraints (Simple info) -> Simple info result -> result
solveSimple = solveConstraints evalSimple
 
instance Show FiniteMapSubstitution where
   show _ = "<FiniteMapSubstitution>"
   
instance ConstraintInfo info => IsSolver (Simple info) info where
   
   findSubstForVar i = 
      do s <- get
         let sub = getWith id s
         return (sub |-> TVar i)
         
   unifyTerms info t1 t2 =
       do  t1'     <- applySubst t1
           t2'     <- applySubst t2
           options <- getSolverOptions
           let synonyms = getTypeSynonyms options       
           case mguWithTypeSynonyms synonyms t1' t2' of
               Right (used,sub) -> 
                   modify (liftFunction (sub @@))
               Left _ -> addError info
