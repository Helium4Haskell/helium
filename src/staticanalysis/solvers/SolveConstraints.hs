-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveConstraints.hs : A framework to solve a set of type constraints. 
--    Known instances of "ConstraintSolver":
--       - SolveGreedy
--       - SolveEquivalenceGroups (with type graphs)
--
-------------------------------------------------------------------------------

module SolveConstraints
   ( ConstraintSolver(..), module SolveState
   , applySubst, getReducedPredicates
   , runSolver, RunnableSolver
   , SolverOption(..), SolverOptions
   ) where
   
import ConstraintInfo ( ConstraintInfo, setOriginalTypeScheme )
import Constraints    ( Constraints, Constraint(..)           )
import Monad          ( unless )
import SolverOptions  
import Types     
import SolveState

class ConstraintSolver solver info where
   initialize        ::                     SolveState solver info ()
   makeConsistent    ::                     SolveState solver info ()
   unifyTerms        :: info -> Tp -> Tp -> SolveState solver info ()
   newVariables      :: [Int] ->            SolveState solver info ()
   findSubstForVar   :: Int ->              SolveState solver info Tp

   initialize     = skip    -- default definition (do nothing)
   makeConsistent = skip    -- default definition (do nothing)
   newVariables _ = skip    -- default definition (do nothing)

--------------------------------------
-- Algorithm to solve the type constraints

solve :: (ConstraintInfo info,ConstraintSolver solver info) => Int -> Constraints info -> SolveState solver info ()
solve unique constraints =
   do setUnique unique      
      initialize
      mapM_ solveOne constraints
      makeConsistent      

solveOne :: (ConstraintInfo info,ConstraintSolver solver info) => Constraint info -> SolveState solver info ()
solveOne constraint =
  case constraint of

   Equiv info t1 t2 -> 
      do unifyTerms info t1 t2

   ExplInstance (f1,f2) tp ts -> 
      do unique <- getUnique
         let (unique',predicates,its) = instantiate unique ts
             info'                    = setOriginalTypeScheme ts (f1 (its,tp))
         setUnique unique'
         newVariables [unique..unique'-1]
         mapM_ solveOne [ PredConstraint (f2 p) p | p <- predicates ]
         solveOne (Equiv info' tp its)         

   ImplInstance info t1 m t2 -> 
      do makeConsistent
         t2' <- applySubst t2
         m'  <- mapM applySubst m
         ps  <- getReducedPredicates
         let scheme = generalize (ftv m') (map fst ps) t2'
         solveOne (ExplInstance info t1 scheme)

   PredConstraint info predicate ->
      do addPredicate predicate info
    
   MakeConsistent -> 
      do makeConsistent

getReducedPredicates :: ConstraintSolver solver info => SolveState solver info [(Predicate, info)]
getReducedPredicates = 
   do options     <- getSolverOptions
      predicates  <- getPredicates
      substituted <- let f (Predicate s tp, info) = 
                            do tp' <- applySubst tp
                               return (Predicate s tp', info)
                     in mapM f predicates
      let (reduced, errors) = contextReduction' (getTypeSynonyms options) standardClasses substituted
      mapM_ addError errors
      setPredicates reduced
      return reduced
   
applySubst :: ConstraintSolver solver info => Tp -> SolveState solver info Tp
applySubst (TVar i)     = findSubstForVar i
applySubst tp@(TCon _)  = return tp
applySubst (TApp t1 t2) = do t1' <- applySubst t1
                             t2' <- applySubst t2
                             return (TApp t1' t2')

type RunnableSolver info = Int                     -- unique type variable counter 
                        -> SolverOptions           -- options
                        -> Constraints info        -- list of type constraints
                        -> ( Int                   -- unique counter after solving
                           , WrappedSubstitution   -- substitution 
                           , Predicates            -- type class predicates
                           , [info]                -- type errors to be reported
                           , IO ()                 -- debug information 
                           )                      
     
runSolver :: (ConstraintSolver solver info, ConstraintInfo info) => 
                SolveState solver info WrappedSubstitution -> RunnableSolver info 
runSolver buildSubstitution unique options constraints =
   runState ( do setSolverOptions options
                 solve unique constraints                 
                 u  <- getUnique
                 s  <- buildSubstitution 
                 e  <- getErrors
                 -- e' <- mapM substitute e
                 ps <- getReducedPredicates
                 d  <- getDebug                  
                 return (u,s,map fst ps,e,d)
            )           
{-
    where substitute :: (ConstraintSolver solver info,Substitutable info) => info -> SolveState solver info info
          substitute scheme = do let vs = ftv scheme
                                 ts <- mapM findSubstForVar vs
                                 return $ listToSubstitution (zip vs ts) |-> scheme
-}
