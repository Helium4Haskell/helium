module NestedInfiniteType where

-- the type signature should be: Int -> [Int] -> [Int]
f :: [a] -> [a] -> [a]
f a []     = [a]
f a (x:xs) | a<x  = a:x:xs
           | a==x = a:x:xs
           | a>x  = x:f a xs
