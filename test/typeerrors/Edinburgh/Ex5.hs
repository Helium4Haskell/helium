module Ex5 where

test = \x -> let y = \z -> let wildcard = x z 
                           in (\w -> w)
             in (y 5, y True)
