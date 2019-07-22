module Qual4 where

import Qual1 as Q

f :: Int
f = 2

(/**) :: a -> Int -> Int
_ /** z = 2 * g * z -- 12 * z
  where
    g = 3 * k -- 6
      where
        k = 2

infixr 5 /**

data Listt3 a = a :>>< (Qual4.Listt3 a) 
              | Emptyy

listtest :: Q.Listt3 Prelude.Int
listtest = (Q.f Q./** 5)
                Q.:>>< 
            Q.Emptyy

listtest2 :: Qual4.Listt3 Prelude.Int
listtest2 = (Qual4.f Qual4./** 5)
                Qual4.:>>< 
            Qual4.Emptyy
            
test :: Qual4.Listt3 Int
test = Qual4.listtest