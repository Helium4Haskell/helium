module Bug where

class A a where
    a :: a -> Int

f :: A a => a -> Int -> Int
f _ a = a
