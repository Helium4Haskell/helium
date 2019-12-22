module Qual5(module Qual1) where

import qualified Qual1 as Q

f :: Bool
f = True

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt3 a = a :>>< (Qual5.Listt3 a) 
              | Emptyy