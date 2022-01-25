module Test where

-- class Test a where
--     type T a
--     test :: a -> a

-- instance Test a => Test [a] where
--     type T [a] = a
--     test x = x

-- instance Test Int where
--     type T Int = Int
--     test x = x

-- -- instance Test Int where
-- --     test = id

-- -- instance Test a => Test [a] where
-- --     test = id

-- type family X a = r | r -> a where
--     X Int = Float
--     X Char = String
-- --type instance X Int = Float
-- type family Z a = r | r -> a

type NewInt = Int

main :: NewInt
main = head $ mapPlus1 [1,2,3,4]

mapPlus1 :: [Int] -> [Int]
mapPlus1 = map (\x -> x + 1)

type family F a b = r | r -> a

type family I x

type family G a

class X a where
    type H a

type instance Z Int = Float