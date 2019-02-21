data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool
    XEQ :: a -> a -> X Bool

f :: X a -> Bool
f (I i) = i == 3
f (B b) = b
f (XEQ x y) = x == y