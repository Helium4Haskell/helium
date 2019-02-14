class X a where
    f :: a -> Int

instance X Int where
    f x = x + 1

instance X a => X [a] where
    f [] = 0
    f (x:xs) = f x + f xs

main = f [1..5]