module PMC6 where

data MyTuple2 a b = MyTuple2 a b

main :: Int
main = 0

headAndList :: [a] -> MyTuple2 a [a]
headAndList l@(h:_) = MyTuple2 h l