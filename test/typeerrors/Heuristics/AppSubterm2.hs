module AppSubterm2 where

f :: Int -> Int -> Int -> Int
f a b c = 2 * (2 * a + b) + c 

main :: Int -> Int
main x = f 0 (x==1) x
