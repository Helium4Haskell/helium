module Qual6 where

import Qual5

test :: Bool
test = f
{-
f :: Int
f = 2

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt3 a = a :>>< (Qual5.Listt3 a) 
              | Emptyy
-}