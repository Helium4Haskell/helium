module AppInsert2 where

sumInts :: [Int] -> Int
sumInts xs = foldr (+) xs
