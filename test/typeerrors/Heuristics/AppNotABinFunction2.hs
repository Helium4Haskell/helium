module AppNotABinFunction2 where

test :: Bool -> Bool -> Bool
test x y = (x && y) `not` (x || y)
