module TupleReorder2 where

shuffle :: (a,b,c) -> (b,c,a)
shuffle (a,b,c) = (b,c,a)

main :: (Int,Int,Bool)
main = shuffle (1,True,2)
