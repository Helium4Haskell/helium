module TestCollectFunBinds where



main :: Int
main = 0

a [] = 0
a (x:xs) = 1

b = 3
b = 4

a = 5

c () = 7
c (x, y) = 8
c (x, y, z) = 9

d = let x = 3; x = 4; y = 5 in 6