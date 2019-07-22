module Qual1 where

f :: Int
f = 2

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt a = a :> (Listt a) | Empt

mylist :: Listt a
mylist = Empt

data Listt2 a = a :>< (Listt2 a) | Empty

data Listt3 a = a :>>< (Qual1.Listt3 a) | Emptyy

listtest :: Qual1.Listt3 Prelude.Int
listtest = (Qual1.f Qual1./** Qual1.f)
                Qual1.:>>< 
            Qual1.Emptyy
