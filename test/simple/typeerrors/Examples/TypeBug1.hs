module TypeBug1 where                                                             
                                                                                
f :: a -> a -> [(a,b)] -> Bool                 
f x = f
