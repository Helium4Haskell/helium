module TypeBug5 where

f :: [[String]]->[String]
f (x:xs) = x ++ filter (not(eqString unwords(concat x xs))) xs

eqString :: String -> String -> Bool
eqString = (==)

