module Export18(module Export18, module ExportBasic2) where

--import ExportBasic
import ExportBasic2

f :: Int
f = 4

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 3

infixr 6 /**

data Listt a = a :> a | Empty

type Hello = Int