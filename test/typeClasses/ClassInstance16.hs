class X a where
    f :: a -> Int 
    f _ = 7

class (X a, Eq a) => Mixed a

instance X Int

instance Mixed Int 

g :: Mixed a => a -> Bool
g x = f x == 7

main = g 3