module InfiniteOrNot where

f :: Int -> [Int]
f x = [x]

main [] = 0
main (x:xs) = [sum x, main xs]
