class X a where
    f :: a -> Int

instance X Int where
    f x = x + 1

instance X a => X [a] where
    f [] = 0
    f (x:xs) = f x + f xs

instance X a => X (Maybe a) where
    f Nothing = 0
    f (Just n) = f n * 10
    

main = f $ map Just [1..5]