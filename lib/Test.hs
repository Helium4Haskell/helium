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
main = head $ mapPlus1 [1,2,3, f 4]

mapPlus1 :: [Int] -> [Int]
mapPlus1 = map (\x -> x + 1)

type family F a b = r | r -> a

type family I a b

-- type family G a

class X a where
    type Q a b

instance X Int where
    type Q Int Int = Float

-- type family J a b where
--     J Int Int = Float
--     J Int Int = Int

type family G a = r | r -> a where
    G Int = Bool
    G Bool = Int
    G a = a

-- type family Z a = r | r -> a
-- type instance Z [a] = (a, a)
-- type instance Z (Maybe b) = (b, [b])

-- type family G6 a = r | r -> a
-- type instance G6 [a] = [G a]
-- type instance G6 Bool = Int

-- type family G a = r | r -> a

-- type family UU a where
--     UU String = Char
--     UU Float = Int
--     UU [a] = Int

-- type instance I Int a = J a a

data Tree a = Node a (Tree a) (Tree a) | Leaf

-- f :: I Int
-- f = Leaf

-- type instance I Int a = a
-- type instance I a Int = a

-- type family G4 a b = r | r -> a b
-- type instance G4 a b = [a]

type family C a b where
    C a b = Int
    C Int Int = Float
    C Int a   = Int

-- type instance E Int = Float
-- type instance E Float = Int
-- type instance E Float = Float

f :: G Bool -> G Bool
f x = x