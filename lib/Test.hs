module Test where

class Test a where
    test :: a -> a

instance Test Int where
    test = id

instance Test a => Test [a] where
    test = id

main :: Int
main = 4 + 5