class X a where
    f :: a -> Int
    g :: a -> Int

instance X Int where
    g = id

main = g 3