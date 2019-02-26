class X a where
    f :: a -> Int

instance X (Maybe a) where
    f n = n

main = f (Just 3)