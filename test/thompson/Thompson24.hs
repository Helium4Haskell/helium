compress :: [a] -> [a] 
compress [] = [] 
compress [a] = [a] 
compress (x:y:xs) 
    | (x == y)  = compress (x:xs) 
    | otherwise = x : compress (y:xs) 
{- Helium does not have a class Eq -}
