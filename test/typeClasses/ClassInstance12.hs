class X a where
    f :: a -> Int

class X a => Y a where
    g :: a -> (Int, Int)

instance X Int where
    f = (+1)

instance Y Int where
    g x = (f x, -f x)

main = g 3