module Comprehension2 where

main :: [[Char]]
main = [ [x,y,z] | x@'a' <- "abc", let { z :: Char; z = x }, y <- "xy" ]
