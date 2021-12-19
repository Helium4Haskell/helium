module Test where

class Test a where
    type T a
    test :: a -> a

instance Test a => Test [a] where
    type T [a] = a
    test x = x

instance Test Int where
    type T Int = Int
    test x = x

-- instance Test Int where
--     test = id

-- instance Test a => Test [a] where
--     test = id

type family X a = r | r -> a where
    X Int = Float
    X Char = String
--type instance X Int = Float
type family Z a = r | r -> a

main :: Int
main = 4