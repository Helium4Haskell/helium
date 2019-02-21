data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool

f :: X a -> a
f (I i) = i
f (B b) = b