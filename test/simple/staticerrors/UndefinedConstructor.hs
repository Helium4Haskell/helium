module UndefinedConstructor where

data Tree a = Bin (Tree a) (Tree a) 
            | Leaf a
            
main :: Tree Int
main = Binn (Leaf 3) (Leaf 5)            
