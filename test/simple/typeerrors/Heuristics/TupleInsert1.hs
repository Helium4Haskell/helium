module TupleInsert1 where

ifthenelse :: (Bool,a,a) -> a
ifthenelse (b,t,e) = if b then t else e

main :: Int
main = ifthenelse (5,3)
