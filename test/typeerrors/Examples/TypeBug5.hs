module TypeBug5 where

f :: [[String]]->[String]
f (x:xs) = x ++ filter (not((==) unwords(concat x xs))) xs
