data X a where
    A :: (b -> Int) -> b -> X Int

f :: X a -> a
f (A f x) = x
