module TypeBug2 where


f :: a -> [a] -> [a]
f sep (x:xs) = x:sep++f xs 
