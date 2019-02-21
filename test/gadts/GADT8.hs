data X a where
    I :: Int -> X Int
    B :: Bool -> X Bool
    XEQ :: a -> a -> X Bool

f :: X a -> X b -> Int 
f x y = case x of 
        I a -> case y of 
            I b -> a + b
            B b -> a + b