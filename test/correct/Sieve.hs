module Sieve where

main :: [Int]
main = take 1000 (sieve [2..])

sieve :: [Int] -> [Int]
sieve (x:xs) 
   = x 
   : sieve (filter (nietVeelvoud x) xs)
   
nietVeelvoud :: Int -> Int -> Bool
nietVeelvoud x y = y `mod` x /= 0
