module TypeBug6 where

f :: [[String]]->[String]
f [x]     = []
f [x,y]   = x ++ filter (not.eqString (unwords(concat x y))) y
f (x:y:z) = f (x:y) ++ f (x:z)
