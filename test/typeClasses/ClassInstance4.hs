class X a where
    f :: Int -> a

class X a => Y a where
    g :: Char -> a
    
instance X Int where
    f = (+1)

instance Y Int where
    g = f . primOrd

main = show (g 'a' + 1)