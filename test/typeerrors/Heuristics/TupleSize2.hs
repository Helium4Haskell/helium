module TupleSize2 where

f :: [a] -> [b] -> a
f as bs = let (x,y,z) = head (zip as bs)
          in x
