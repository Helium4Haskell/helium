module FunArity2 where

zipp [] = []
zipp [] ys = []
zipp xs [] = []
zipp (x:xs) (y:ys) = (x, y) : zipp xs ys
