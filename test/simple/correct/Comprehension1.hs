module Comprehension1 where

main :: [[Char]]
main = [ [x,y,z] | x <- "abc", isA x, let { z = x }, y <- "xy" ]

isA :: Char -> Bool
isA 'a' = True
isA 'b' = True
isA _ = False
