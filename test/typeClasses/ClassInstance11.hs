class Y a where
    g :: a -> Char

class Y d => X d where
    f :: d -> Int

instance Y Int where
    g x = primChr (f x)

instance X Int where
    f x = x + 1

instance Y Char where
    g = id

instance X Char where
    f = primOrd

instance X g => X [g] where
    f [] = 0
    f (x:xs) = f x + f xs 

instance Y g => Y [g] where
    g [] = 'a'
    g (x:xs) = primChr (primOrd (g x) +  primOrd (g xs))
       

instance X z => X (Maybe z) where
    f Nothing = 0
    f (Just n) = f n * 10

instance Y z => Y (Maybe z) where
    g Nothing = 'a'
    g (Just n) = g n

instance (X b, X a) => X (a, b) where
    f (x, y) = f x * f y

instance (Y b, Y a) => Y (a, b) where
    g (x, y) = primChr (primOrd (g x) + primOrd (g y) - 650)

main = g (map Just [1..5], "hello")