module Ex7 where

test = \z -> let x = z
             in let y = z 1 
                in x True
