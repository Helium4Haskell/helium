class X a where
    f :: a -> Int

instance X Int

main = f 3