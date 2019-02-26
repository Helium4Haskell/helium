
class X d where
    f :: d -> Int

instance X Int where
    f x = x + 1

instance X Char where
    f = primOrd

instance X g => X [g] where
    f [] = 0
    f (x:xs) = f x + f xs

instance X z => X (Maybe z) where
    f Nothing = 0
    f (Just n) = f n * 10

instance (X b, X a) => X (a, b) where
    f (x, y) = f x * f y

main = f (map Just [1..5], "hello")