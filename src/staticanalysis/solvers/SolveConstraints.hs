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
   , applySubst, runSolver, RunnableSolver
   , SolverOption(..), SolverOptions
   ) where
   
import ConstraintInfo ( ConstraintInfo, setOriginalTypeScheme )
import Constraints    ( Constraints, Constraint(..)           )
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

   ExplInstance info tp ts -> 
      do unique <- getUnique
         let (unique',its) = instantiate unique ts
             info'         = setOriginalTypeScheme ts (info (its,tp))
         setUnique unique'
         newVariables [unique..unique'-1]
         solveOne (Equiv info' tp its)

   ImplInstance info t1 m t2 -> 
      do makeConsistent
         t2' <- applySubst t2
         m'  <- mapM applySubst m
         let scheme = generalize (ftv m') t2'
         solveOne (ExplInstance info t1 scheme)
         
   MakeConsistent -> 
      do makeConsistent 
   
applySubst :: ConstraintSolver solver info => Tp -> SolveState solver info Tp
applySubst (TVar i)     = findSubstForVar i
applySubst tp@(TCon _)  = return tp
applySubst (TApp t1 t2) = do t1' <- applySubst t1
                             t2' <- applySubst t2
                             return (TApp t1' t2')                                   

type RunnableSolver info = Int                  -- unique type variable counter 
                        -> SolverOptions        -- options
                        -> Constraints info     -- list of type constraints
                        -> ( Int                -- unique counter after solving
                           , Subst              -- substitution 
                           , [info]             -- type errors to be reported
                           , IO ()              -- debug information 
                           )                      
     
runSolver :: (ConstraintSolver solver info, ConstraintInfo info) => 
                SolveState solver info Subst -> RunnableSolver info 
runSolver buildSubstitution unique options constraints =
   runState ( do setSolverOptions options
                 solve unique constraints                 
                 u  <- getUnique
                 s  <- buildSubstitution 
                 e  <- getTypeErrors
                 -- e' <- mapM substitute e
                 d  <- getDebug                  
                 return (u,s,e,d)                                
            )           
{-
    where substitute :: (ConstraintSolver solver info,Substitutable info) => info -> SolveState solver info info
          substitute scheme = do let vs = ftv scheme
                                 ts <- mapM findSubstForVar vs
                                 return $ listToSubstitution (zip vs ts) |-> scheme
-}
