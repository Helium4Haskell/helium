x :: Eq a => a -> a
x = id

y = let f :: (Ord a, Num a) => a 
        f = f
    in 3

s = 3 :: Num a => a

a, b :: Show a => a
a = 3
b = 4


ditMagOok :: () => Int
ditMagOok = 42
