module SameTypesInTypeError where

contains::String -> [String] -> Bool
contains x s | (s == []) = False
             | (x == head s) = True
             | otherwise = contains x (tail s)
