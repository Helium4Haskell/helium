module TupleSize1 where

f :: Int -> (Int,Int)
f 0 = (1,1)
f i = let (a,b) = f (i-1)
      in (a+b,a,b)
