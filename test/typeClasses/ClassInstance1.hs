class X a where
    f :: a -> Int

instance X Int where
    f = id

instance X Char where
    f x = primOrd x

main = show (f 3) ++ show (f 'a')