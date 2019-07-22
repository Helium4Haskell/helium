class X a where
    f :: a -> Bool

class Y a where
    g :: a -> Bool
    g = f