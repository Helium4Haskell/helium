module PMC8 where

main :: Int
main = lengte (filter even [1..1000])

lengte :: [a] -> Int
lengte xs =
    len xs 0
    
len :: [a] -> Int -> Int
len xs n = 
    case xs of
        []   -> n
        y:ys -> len ys $! (n + 1)
