class X a where
    f :: a -> Int

instance X a where
    f n = n

main = f 'a'