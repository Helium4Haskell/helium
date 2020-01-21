module Record where

data A4 a b  = A4 { a4 :: a, b4 :: b }
             | B4 { a4 :: a }

p :: A4 b c -> A4 b String
p x = x { b4 = "ASDSADA" }

q :: String
q = "String"

main :: IO ()
main = error (b4 (p undefined))
-- main = error (id q)
