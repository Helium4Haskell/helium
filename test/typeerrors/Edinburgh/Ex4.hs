module Ex4 where

test = let f = \x -> let y = x 
                     in y 5 
       in f 3
