f :: int -> bool
f i = i == 0

g :: a -> a
g = id

depth :: tree -> Int
depth tree  = 
   case tree of
      Node l r -> 1 + (depth l `max` depth r)
      Leaf _   -> 1

data Tree = Node Tree Tree | Leaf Int
data A    = A
