maxFour :: Int -> Int -> Int -> Int -> Int 
maxFour 
    | a >= b && a >= c && a >= d  = a 
    | b >= c && b >= d            = b 
    | c >= d                      = c 
    | otherwise                   = d 
