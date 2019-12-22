module ExportBasic2(module ExportBasic2) where

f :: Int
f = 3

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt a = a :> (Listt a) | Empt

data Listt2 a = a :>< (Listt2 a) | Empty

data Listt3 a = a :>>< (Listt3 a) | Emptyy

listtest :: Listt3 a
listtest = Emptyy

type Hello = Bool