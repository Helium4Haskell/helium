module ManyConstructs where

-- Check whether we can compile these constructs 
-- without (most of) the Prelude. 

-- Can't test this anymore because import lists are forbidden...

-- import Prelude((>), (+), unsafePerformIO, putChar) -- , dictNumInt, dictOrdInt)

data A = A Int String

main :: ([Int], [Int], Int, Int, [Int], A, ())
main = -- primUnsafePerformIO, primPutStrLn, primShowTuple8 in inserted main
    (   [1..5] -- primEnum...
    ,   [1,3..10]
    ,   case [1..] of (y:_) -> y
    ,   case [3,5..] of (_:_:y:_) -> y
    ,   [ y | x <- [1..10], x > 5, let { y :: Int; y = x + 1 }] -- primConcatMap
    ,   A 3 "bla" -- primConcat
    ,   unsafePerformIO (do { putChar 'a'; putChar 'b' }) -- primBindIO
    )
