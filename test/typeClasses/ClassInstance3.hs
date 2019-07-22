data Y = Y Int
    deriving Show

class X a where
    f :: Int -> a

instance X Y where
    f = Y

main = show (f 3 :: Y)