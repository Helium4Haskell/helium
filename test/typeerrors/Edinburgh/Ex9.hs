module Ex9 where

f5 0 n = []
f5 m n = (m ^^^ n) : f5 (m-1)

-- string concatenation in ML (symbol '^')
(^^^) :: String -> String -> String
x ^^^ y = x ++ y
