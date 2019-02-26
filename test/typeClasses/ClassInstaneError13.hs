class X a where
    f :: a -> Int

class Y a where
    g :: a -> Bool
    g = f