class X a where
    f :: a -> Int

instance X Char where
    f n = n

main = f 'a'