module SuspiciousFBs where

fun x  = x
funs x = [x]

test = let suspicious :: Int -> Bool
           suspiciuos 0 = True
           suspicious 1 = False
           suspicious n = suspicious (n-1)
       in undefined         


deleteIndex :: Int -> [a] -> [a]
deleteIndex _ []     = []
deleteIndex 0 (a:as) = as
deleteindex i (a:as) = a : deleteIndex (i-1) as
