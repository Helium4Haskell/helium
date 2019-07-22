class X a where
    f :: a -> Int

instance X Char where
    f _ = 5

main = f 3