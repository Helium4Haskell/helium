class X a where
    f :: a -> Int

class X a => Y a where
    g :: a -> Bool
    g = f