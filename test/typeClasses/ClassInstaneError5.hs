class X a where
    f :: a -> Int
    f = id

instance X Int where
    f n = 'a'

main = f 3