module Helium.Optimization.Utils where

import Control.Monad.State.Lazy (State, evalState, get, put, liftM2)

type Fresh a = State Int a

runFresh :: Fresh a -> a
runFresh = flip evalState 0

listAdd :: Fresh [a] -> Fresh [a] -> Fresh [a]
listAdd = liftM2 (++)

freshList :: Fresh [a]
freshList = return []

fresh :: Fresh Int
fresh = do
    x <- get
    put $ x + 1
    return x