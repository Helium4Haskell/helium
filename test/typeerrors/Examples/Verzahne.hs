-- Bug: reported by Jan Scheffczyk, November 2004.
verzahne :: ( [a] -> [a]  -> Bool) -> [a] -> [a] -> [a]
verzahne _ xs [] = xs
verzahne _ [] ys = ys
verzahne le (x:xs) (y:ys)
     | x `le` y = x : (verzahne le xs (y:ys))
     |otherwise = y : (verzahne le (x:xs) ys)
