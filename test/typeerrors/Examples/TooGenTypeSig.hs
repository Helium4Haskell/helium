module TooGenTypeSig where

test x = let f :: a -> [a] 
             f y = [x,y]
         in f
