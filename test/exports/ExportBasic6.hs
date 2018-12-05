module ExportBasic6(Listt6((:>)), Listt6(Empty), div, z, (+)) where

import Prelude hiding ((+))
import ExportBasic3

f :: Int
f = 4

(/**) :: a -> Int -> Int
_ /** l = 2 * g * l -- 18 * l
  where
    g = 3 * k -- 9
      where
        k = 3

infixl 6 /**

data Listt6 a = a :> (Listt6 a) | Empty

type Hello2 = Int

(+) :: Int -> Int -> Int
_ + _ = 5