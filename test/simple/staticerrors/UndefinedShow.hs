module UndefinedShow where

data Tree a = Bin (Tree a) (Tree a)
            | Leaf a
            
main = showTreee (Bin (Leaf 32434) (Leaf 123))
