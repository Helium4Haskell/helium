module TupleReorder1 where

f :: (Int,Bool) -> Int
f (i,b) = if b then i else 0

main :: Int
main = f (True,5)
