module TupleRemove1 where

f :: Int -> (Int,Int)
f 0 = (1,1)
f i = let (a,b) = f (i-1)
      in if a == b 
           then (True,a+b,a)
           else (a,b)
