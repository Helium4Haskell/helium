ascendingOrder :: Int -> Int -> Bool 
ascendingOrder a b 
    | a<=b      = a b 
    | otherwise = b a 
