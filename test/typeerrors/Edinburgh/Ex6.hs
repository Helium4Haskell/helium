module Ex6 where

test = \x -> let f = \y -> y x
             in (f (\z -> z)) (f (\u -> \v -> u))
