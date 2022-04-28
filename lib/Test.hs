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

-- main :: Int
-- main = f 4

-- mapPlus1 :: [Int] -> [Int]
-- mapPlus1 = map (\x -> x + 1)

type family F a b = r | r -> a

-- type family I a b

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

-- type family C a b where
--     C a b = Int
--     C Int Int = Float
--     C Int a   = Int

-- type instance E Int = Float
-- type instance E Float = Int
-- type instance E Float = Float

-- f :: G a -> G a
-- f x = x

-- f2 :: Int
-- f2 = f 3

-- type family FloatInt a b where
--     FloatInt a a = Float
--     FloatInt a b = Int

-- type family IfFloat a where
--     IfFloat Float = Int -> Int
--     IfFloat Int   = String

-- bad :: d -> IfFloat (FloatInt Float [d])
-- bad _ = "Hi"

-- fault :: Int
-- fault = bad (0.2 :: Float) (5 :: Int)

-- l :: J String -> J String
-- l x = x

type family H a b where
    H Float Int = Int
    H Int Float = String
    --H Float Int = Float

type family J a where
    J Int = Int
    J Float = Float

-- type family I a b c where
--     I Float Float Int = String
--     I Float Int Float = Float

-- -- h :: String -> String -> H (J (J Int)) Int
-- -- h s1 s2 = s1 ++ s2 ++ "hi"

-- h3 :: H (H Int Float) (H Int Int)
-- h3 = "Hi"

h2 :: H Int Int -> H Float Int
h2 x = "Hi" ++ x
-- h1 :: I Float Int Float
-- h1 = "Hi"

-- type family Loop a where
--     Loop [a] = Loop a
--     Loop a = a 

-- g :: Loop [[[[[[[String]]]]]]]
-- g = "Hi"

-- type family Loop a where
--     Loop [a] = Loop a
--     Loop a = a
--     --Loop Int = Bool

-- g :: Loop [[[[[[[a]]]]]]]
-- g = True

--h = g + g
-- Int -> Int > h_
-- h :: Int -> Int
-- h = id

-- k :: Eq a => a -> a -> Bool
-- k x y = x == y

-- type family K a
-- type instance K Int = Int

-- j :: a -> (a, Int)
-- j x = (0, x)

-- data X a where
--     A :: Bool -> X Bool
--     B :: Int -> X Int

-- g (A x) = x
-- g (B x) = x

-- data X a where
--     A :: Bool -> X Bool
--     B :: Int -> X Int

-- g :: X Int -> Int
-- g (A x) = x
-- g (B y) = y

-- g :: [a] -> [a] -> a
-- g xs ys = sum (xs ++ ys)

-- type family B a = r | r -> a
-- type instance B Int = Float
-- type instance B Float = Int

-- f :: B a -> Int
-- f x = x

-- g :: Int -> B a
-- g x = x

-- type family Right w z
-- type instance Right w z = z

-- type family Id d
-- type instance Id d = d

-- -- right :: a -> b -> Right a (Id b)
-- -- right x y = x

-- id2 :: a -> b -> Right a (Id b)
-- id2 x y = x

-- type family Foo a b c = r | r -> c
-- type instance Foo Char Char Char = Bool
-- type instance Foo Char Char Char = Bool
-- type instance Foo Float Bool Int = Int

-- class Bar t where
--   clsF :: Foo t (Id v) t
-- instance Bar Char where
--   clsF = True

-- main :: Bool
-- main = clsF :: Bool

-- type family Foo a 
-- type instance Foo Char = Bool
-- type instance Foo Char = Bool
-- type instance Foo Float = Int

-- class Bar t where
--   clsF :: Foo t
-- instance Bar Char where
--   clsF = True

-- main :: Bool
-- main = clsF :: Bool

-- type family Foo a 
-- type instance Foo Char = Bool
-- type instance Foo Int = Float
-- type instance Foo Float = Int

-- -- clsf :: Foo t
-- -- clsf = True

-- main :: Bool
-- main = clsF

-- class Bar t where
--     clsF :: Foo t
-- instance Bar Char where
--     clsF = True
