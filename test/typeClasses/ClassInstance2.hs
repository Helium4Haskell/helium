class X a where
    f :: a -> Int
    g :: a -> Char
    g = primChr . f
    f = primOrd . g

instance X Int where
    f = id

instance X Char where
    g = id

main = show (f 3) ++ show (f 'a')