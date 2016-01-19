-- test1 [3] [3] gives True as expected, but
-- test2 [3] [3] gives False.
-- Also happens in the case of tuples.


test1 :: Eq a => a -> a -> Bool
test1 x y = x == y

test2 :: Ord a => a -> a -> Bool
test2 x y = x == y

