f :: [[String]] -> String
f (x:_) = x ++ replicate (length x) ' '