module Case1 where

main :: Int
main = 
    case [2,2] of
        (1:y:ys) -> y + 3
        (x:xs) -> 32
   