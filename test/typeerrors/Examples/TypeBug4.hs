module TypeBug4 where

sp :: ([a] -> Int -> String) -> [a] -> String
sp k l | length k <# maxInt length k (maxInt.map(length l)) = k : sp k : " "
       | True                                               = k

maxInt :: Int -> Int -> Int
maxInt = max

(<#) :: Int -> Int -> Bool
(<#) = (<)