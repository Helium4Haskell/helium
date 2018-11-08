class X a where
    f :: a -> Int

instance X Int where
    f n = [n]

main = f 3