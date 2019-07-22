class X a where
    f :: a -> Int
    f _ = 7

instance X Char

instance X Int where
    f = id

main = show (f 'a') ++ show (f 3)