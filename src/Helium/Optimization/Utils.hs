module Helium.Optimization.Utils where

import Control.Monad.State.Lazy (State, runState, evalState, get, put, liftM2)

{- Debug imports -}
import Text.PrettyPrint.Leijen (Pretty, pretty)
import qualified Debug.Trace as Trace(trace)

{- 2Tuple -}
mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f (a,b) = (f a,b)
mapSnd :: (b -> c) -> (a,b) -> (a,c)
mapSnd f (a,b) = (a,f b)

{- 3Tuples -}
first :: (a,b,c) -> a
first (a,_,_) = a

second :: (a,b,c) -> b
second (_,b,_) = b

third :: (a,b,c) -> c
third (_,_,c) = c

{- Fresh Monad -}
type Fresh a = State Int a

runFresh :: Fresh a -> a
runFresh = flip evalState 0

runFreshFrom :: Int -> Fresh a -> (a,Int)
runFreshFrom x = flip runState x

listAdd :: Fresh [a] -> Fresh [a] -> Fresh [a]
listAdd = liftM2 (++)

freshList :: Fresh [a]
freshList = return []

fresh :: Fresh Int
fresh = do
    x <- get
    put $ x + 1
    return x

getFresh :: Fresh Int
getFresh = do
    x <- get
    return x

putFresh :: Int -> Fresh ()
putFresh x = do
    put x

{- Debugging -}
trace :: String -> a -> a
trace = Trace.trace

traceShow :: Show a => String -> a -> a
traceShow s x = trace (s ++ ":" ++ show x) x

tracePretty :: Pretty a => String -> a -> a
tracePretty s x = trace (s ++ ":" ++ (show $ pretty x)) x
