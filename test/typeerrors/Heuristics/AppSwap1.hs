module AppSwap1 where

isEven :: Int -> Bool
isEven i = [0,2..] `elemInt` i

elemInt :: Int -> [Int] -> Bool
elemInt i []     = False
elemInt i (x:xs) = i == x || elemInt i xs               
