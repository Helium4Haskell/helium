module RightSection where

test :: [Int]
test = filter (False `eqBool`) [1..10]
