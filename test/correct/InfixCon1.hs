module InfixCon1 where

data Tree a = Leaf a | Tree a :+: Tree a

main :: Int
main = firstLeaf (Leaf 3 :+: Leaf 4)

firstLeaf :: Tree a -> a
firstLeaf (Leaf x) = x
firstLeaf (l :+: _) = firstLeaf l
