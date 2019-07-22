class X a where
    f :: a -> Bool

instance Num a => X (Maybe a) where
    f Nothing = True
    f (Just x) = f x == 3

main = f (Just 3)