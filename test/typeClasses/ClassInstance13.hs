class X a where
    f :: a -> Int

class X a => Y a where
    g :: a -> (Int, Int)

instance X Int where
    f = (+1)

instance Y Int where
    g x = (f x, -f x)

instance X a => X [a] where
    f [] = 0
    f (x:xs) = f x + f xs

instance Y a => Y [a] where
    g [] = (0, 0)
    g (x:xs) = (f x, f xs)

a :: Y a => a -> Int
a x = f x

main = a [1..5]