module ExportBasic5(module ExportBasic5,) where

import ExportBasic2

f :: Int
f = 4

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 18 * z
  where
    g = 3 * k -- 9
      where
        k = 3

infixl 6 /**

data Listt5 a = a :> a | Empty

type Hello2 = Int

(+) :: Int -> Int -> Int
_ + _ = 5