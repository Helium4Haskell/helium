-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveState.hs : A state monad in which the constraint solvers can be run.
--
-------------------------------------------------------------------------------

module SolveState
   ( SolveState                              -- SolveState data type
   , runState, skip                          -- standard functionality
   , getUnique, setUnique                    -- unique counter for type variables
   , setSolver, useSolver, updateSolver      -- representation of a substitution
   , setErrors, getErrors, addError          -- errors
   , getSolverOptions, setSolverOptions      -- solver options
   , getDebug, addDebug                      -- debug IO
   , getClassPredicates, addClassPredicates
   , setClassPredicates                      -- type classes
   ) where

import TypeClasses    ( ClassPredicates )
import SolverOptions  ( SolverOptions )
import Utils          ( internalError )
import ST

-------------------------------------------------
--- SolveState data type

newtype SolveState
           solver                            -- a datastructure in which the type constraints can be solved
           info                              -- information that is carried by each type constraint
           result                            -- the result of a computation in this Monad
 = S ( forall state .
        ( STRef state Int                    -- unique counter for type variables
        , STRef state (solver info state)    -- representation of a substitution
        , STRef state [info]                 -- error messages
        , STRef state SolverOptions          -- solver options
        , STRef state ClassPredicates        -- type classes
        , STRef state (IO ())                -- debug IO
        ) ->
        ST state result )

-------------------------------------------------
--- standard functionality

instance Monad (SolveState solver info) where
   return x = S (\_ -> return x)
   (S f) >>= g = S (\tuple -> do result <- f tuple
                                 let (S h) = g result
                                 h tuple )

runState :: SolveState solver info result -> result
runState (S f) =
   runST (do uniqueRef   <- newSTRef 0
             subRef      <- newSTRef (internalError "SolveState.hs" "runState" "solver is not initialized")
             errorsRef   <- newSTRef []
             typeSynsRef <- newSTRef []
             predRef     <- newSTRef []             
             ioRef       <- newSTRef (putStrLn "--- Debug Constraint Solving ---")
             result      <- f (uniqueRef,subRef,errorsRef,typeSynsRef,predRef,ioRef)
             return result)

skip :: SolveState solver info ()
skip = do return ()

-------------------------------------------------
--- unique counter for type variables

getUnique :: SolveState solver info Int
getUnique = S (\(ru,rs,re,rt,rp,ri) -> do readSTRef ru)

setUnique :: Int -> SolveState solver info ()
setUnique u = S (\(ru,rs,re,rt,rp,ri) -> do writeSTRef ru u)

-------------------------------------------------
--- representation of a substitution

setSolver :: (forall state . ST state (solver info state)) -> SolveState solver info ()
setSolver stsolver = S (\(ru,rs,re,rt,rp,ri) -> do solver <- stsolver; writeSTRef rs solver)

useSolver :: (forall state . solver info state -> ST state result) -> SolveState solver info result
useSolver f = S (\(ru,rs,re,rt,rp,ri) -> do solver <- readSTRef rs ; f solver)

updateSolver :: (forall state . solver info state -> ST state (solver info state)) -> SolveState solver info ()
updateSolver f = S (\(ru,rs,re,rt,rp,ri) -> do solver <- readSTRef rs ; solver' <- f solver; writeSTRef rs solver')

-------------------------------------------------
--- errors

setErrors :: [info] -> SolveState solver info ()
setErrors xs = S (\(ru,rs,re,rt,rp,ri) -> do writeSTRef re xs)

getErrors :: SolveState solver info [info]
getErrors = do S (\(ru,rs,re,rt,rp,ri) -> do readSTRef re)
                                          
addError :: info -> SolveState solver info ()
addError e = S (\(ru,rs,re,rt,rp,ri) -> do es <- readSTRef re ;writeSTRef re (e:es))

-------------------------------------------------
--- solver options

getSolverOptions :: SolveState solver info SolverOptions
getSolverOptions = S (\(ru,rs,re,rt,rp,ri) -> do readSTRef rt)

setSolverOptions :: SolverOptions -> SolveState solver info ()
setSolverOptions t = S (\(ru,rs,re,rt,rp,ri) -> do writeSTRef rt t)

-------------------------------------------------
--- type class predicates

getClassPredicates :: SolveState solver info ClassPredicates
getClassPredicates = S (\(ru,rs,re,rt,rp,ri) -> do readSTRef rp)

addClassPredicates :: ClassPredicates -> SolveState solver info ()
addClassPredicates qs = S (\(ru,rs,re,rt,rp,ri) -> do ps <- readSTRef rp ; writeSTRef rp (qs ++ ps))

setClassPredicates :: ClassPredicates -> SolveState solver info ()
setClassPredicates qs = S (\(ru,rs,re,rt,rp,ri) -> do writeSTRef rp qs)

-------------------------------------------------
--- debug IO

getDebug :: SolveState solver info (IO ())
getDebug = S (\(ru,rs,re,rt,rp,ri) -> do readSTRef ri)

addDebug :: IO () -> SolveState solver info ()
addDebug io = S (\(ru,rs,re,rt,rp,ri) -> do io' <- readSTRef ri ; writeSTRef ri (io' >> io))
