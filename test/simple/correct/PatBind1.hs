module PatBind1 where

main :: Int
main = sum xs

x  :: Int
xs :: [Int]
(x:xs) = [1, 2, 3]

y  :: Int
ys :: [Int]
(y:ys) = [4, 5]
