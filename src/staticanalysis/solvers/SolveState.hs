module SolveState 
  ( SolveState
  , getUnique, setUnique
  , getSolverOptions, setSolverOptions
  , newState, extend, liftFunction, getWith
  , module BasicState
  ) where

import           BasicState hiding   (extend, getWith, liftFunction, newState)
import qualified BasicState as State (extend, getWith, liftFunction, newState)
import SolverOptions

type SolveState monad info a = BasicState monad info (SS a)

data SS a = S { counter :: Int, options :: SolverOptions, hiddenExt :: a }

newState :: SolveState monad info ()
newState = State.extend $
              S { counter = 0
                , options = []
                , hiddenExt = () 
                }

instance Show a => Show (SS a) where
   show s = unlines [ "counter = " ++ show (counter s)
                    , show (hiddenExt s)
                    ]

getUnique :: MonadState (SolveState monad info a) monad => 
                monad Int
setUnique :: MonadState (SolveState monad info a) monad => 
                Int -> monad ()

getUnique = gets (State.getWith counter)
setUnique i = modify $ State.liftFunction (\x -> x { counter = i })

getSolverOptions :: MonadState (SolveState monad info a) monad => 
                       monad SolverOptions
setSolverOptions :: MonadState (SolveState monad info a) monad => 
                       SolverOptions -> monad ()

getSolverOptions = gets (State.getWith options)
setSolverOptions opt = modify $ State.liftFunction (\x -> x { options = opt })

liftFunction :: (a -> b) -> SolveState monad info a -> SolveState monad info b
extend       :: a -> SolveState monad info a
getWith      :: (a -> b) -> SolveState monad info a -> b   

liftFunction f = State.liftFunction (\x -> x { hiddenExt = f (hiddenExt x) })
extend       a = liftFunction (const a) newState
getWith      f = f  . State.getWith hiddenExt
