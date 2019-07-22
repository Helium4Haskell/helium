module Qual3 where

import Qual1

f :: Int
f = 2

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt3 a = a :>>< (Qual3.Listt3 a) 
              | Emptyy

listtest :: Listt3 Prelude.Int
listtest = (f /** 5)
                :>>< 
            Emptyy
