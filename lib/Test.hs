module Test where

-- class Test a where
--     test :: a -> a

-- instance Test Int where
--     test = id

-- instance Test a => Test [a] where
--     test = id

type family X a = r | r -> a where
    X Int = Float
    X Char = String
--type instance X Int = Float

main :: Int
main = 4 + 5