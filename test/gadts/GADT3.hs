data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool

f :: X a  -> Int -> a
f (I i) y = i
f (B b) y = y