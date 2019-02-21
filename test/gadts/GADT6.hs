data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool
    XEQ :: a -> a -> X Bool

f :: X a -> X b -> Int 
f (I i) (I j) = i + j