predecessor n :: Int -> Int
predecessor n 
    | n>0  = n-1 
    | n==0 = 0 
{- predecessor n :: Num a => a -> a -}
