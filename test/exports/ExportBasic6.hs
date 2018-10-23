module ExportBasic6(Listt((:>)), Listt(Empty), div, z, (+)) where

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

data Listt a = a :> (Listt a) | Empty

type Hello = Int

(+) :: Int -> Int -> Int
_ + _ = 5