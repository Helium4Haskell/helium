module PMFailure where

main :: Int
main = f 3

f :: Int -> Int
f 1 = 1
f 2 = 2
f 4 = 4
f x | x > 4 = 5

