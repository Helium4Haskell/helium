module TupleRemove2 where

first :: (a,a) -> a
first (a,b) = a

main :: Int
main = first (1,2,"hello","world") 
