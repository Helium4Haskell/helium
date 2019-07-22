class X a where
    f :: a -> Int

instance X Int where
    f x = x + 1

instance X a => X (Maybe a) where
    f Nothing = 0
    f (Just n) = f n * 10

main = f (Just 3)