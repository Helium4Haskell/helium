module AppReorder2 where

sumInts :: [Int] -> Int
sumInts = foldr 0 (+) 
