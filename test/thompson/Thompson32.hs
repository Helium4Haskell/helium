proximity :: a -> a -> Float 
proximity x y = 0.0

q :: b -> Int 
q p = 0 
    where 
    g :: b -> Float 
    g = proximity p 
