module NoTypeDef where

toplevel = 3

f :: Int 
f = let local = 5
    in local
    
g :: a -> a
g x = let monomorph = x
      in x

h :: Int      
h = inWhere
    where inWhere = 4
