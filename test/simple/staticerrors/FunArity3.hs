module FunArity3 where



mymap [] = []
mymap f (x:xs) = f x : mymap f xs
