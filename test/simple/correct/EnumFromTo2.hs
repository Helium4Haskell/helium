module EnumFromTo2 where

main :: [Int]
main = list
  where
    list :: [Int]
    list = take 20 [8,10..]
