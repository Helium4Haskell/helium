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

-- p :: A4 a b -> c -> A4 c b
-- p x c = x { a4 = c }

-- r :: Date
-- r = Date { month = 2, day = 1, year = 0 }

-- q :: A4 a -> c -> A4 a  
-- q x c = x { }

-- q :: Int -> A4 a b d
-- q = undefined
