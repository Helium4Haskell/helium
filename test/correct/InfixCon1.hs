module InfixCon1 where

data Tree a = Leaf a | Combine (Tree a) (Tree a)

main :: Int
main = firstLeaf (Leaf 3 `Combine` Leaf 4)

firstLeaf :: Tree a -> a
firstLeaf (Leaf x) = x
firstLeaf (l `Combine` _) = firstLeaf l
