module EnumFromTo where

main :: [Int]
main = list
  where
    list :: [Int]
    list = take 20 [8,6..]
