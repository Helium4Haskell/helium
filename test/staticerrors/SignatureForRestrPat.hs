x :: Eq a => a -> a -> Bool
y :: Eq a => a -> a -> Bool
z :: Eq a => a -> a -> Bool

(x, _) = undefined
(y) = undefined
z@_ = undefined

f :: Eq a => a -> a -> Bool
f a b = (a == b)

