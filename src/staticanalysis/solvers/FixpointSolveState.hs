module FixpointSolveState where

import Data.STRef
import Control.Monad.ST
import Control.Monad.State
import SolveState

data Fix info extra result = Fix { unFix :: State (SolveState (Fix info extra) info extra) result }

runFix ::  Fix info extra result -> SolveState (Fix info extra) info extra -> (result, SolveState (Fix info extra) info extra)
runFix = runState . unFix

instance Monad (Fix info extra) where
   return x    = Fix (return x)
   Fix f >>= g = Fix (f >>= (unFix . g))

instance MonadState (SolveState (Fix info extra) info extra) (Fix info extra) where
   get = Fix get
   put = Fix . put
