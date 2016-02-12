module ErrIndent where 

 class X a where

   y :: a -> a

   
  class Y b where
   x :: b -> Int
   x _ = 2

