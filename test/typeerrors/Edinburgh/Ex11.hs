module Ex11 where

f4 []    = []
f4 (0:t) = f4 t
f4 (h:t) = h `div` 2.0 : f4 t
