module ParensInfixScope where

f :: a -> b -> c -> (a, b, c)
(as `f` bs) cs  = (as,bs,cs)
