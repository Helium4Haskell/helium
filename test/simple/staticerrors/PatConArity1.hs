module PatConArity1 where



data Tree a = Leaf a | Bin (Tree a) (Tree a)

main = firstLeaf (Bin (Leaf 3) (Leaf 4))

firstLeaf (Leaf x y) = x
firstLeaf (Bin t) = firstLeaf t
