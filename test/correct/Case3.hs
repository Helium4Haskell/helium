module Case3 where

main :: Int
main = f undefined

f :: a -> Int
f xs = 
    case xs of
        x -> 42
        