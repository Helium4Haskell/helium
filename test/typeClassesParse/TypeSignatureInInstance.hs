class SomeClass a where
 plus :: a -> a -> a
 
instance SomeClass Int where
 plus :: Int -> Int -> Int
 plus = (+)
