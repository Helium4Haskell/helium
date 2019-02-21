data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool

f :: X a  -> Int -> Int
f (I i) y = i
f (B b) y = y