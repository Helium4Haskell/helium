module Case2 where

main :: Int
main = 
    case [3,2] of
        (x:y:ys) | z == 2 -> 5
                    where z = x + x
        (x:xs) -> 32
