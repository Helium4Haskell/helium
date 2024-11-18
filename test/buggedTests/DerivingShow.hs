module DerivingShow where

data Listt a = Cons a (Listt a) | Nil

data A = A [Int]

data B a = B (Int -> Int) (Int, Char) A (IO ()) () a (Q Int Bool) (Maybe Int) [[Int]]

type Q a b = (b, a)

main = b

b :: B Int
b = B id (3, 'b') a (putStr "hello") () 3 (True, 5) (Just 42) [[1, 2], [3,4]]
a = A [1,2,3]