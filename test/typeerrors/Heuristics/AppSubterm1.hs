module AppSubterm1 where

main :: [Int]
main = filter p [1 .. 10]
  where p x y = x || y
