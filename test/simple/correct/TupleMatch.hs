module TupleMatch where

main :: Int
main = let (x, y) = (13, x)   in x + y
       -- let (Tup x y) = Tup 13 x in x+y
