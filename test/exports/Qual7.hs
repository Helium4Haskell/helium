module Qual7(module Qual1, f, Listt3(..)) where

import qualified Qual1 as Q
import qualified Prelude as P

f :: Int
f = 2

(/**) :: a -> Int -> Int
_ /** z = 2 P.* g P.* z -- 12 * z
  where
    g = 3 P.* k -- 6
      where
        k = 2

infixr 5 /**

data Listt3 a = a :>>< (Listt3 a) 
              | Emptyy