module SimilarNegation where

test :: Float
test = - (3.0 +. 6.0)

test' :: Int
test' = -. 3

test'' :: Float -> Float
test'' (- 1.0) = 1.0
test'' x       = x +. 1.0

test''' :: Int -> Bool
test''' (-. 1) = True
test''' _      = False
