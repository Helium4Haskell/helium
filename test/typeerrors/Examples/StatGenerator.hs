module StatGenerator where

f :: Bool -> IO Bool -> IO Bool
f x y = do a <- x
           y
