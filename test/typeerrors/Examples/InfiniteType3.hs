module InfiniteType3 where

insert :: (a -> a -> Bool) -> a -> [a] -> [a]
insert f a [] = [a]
insert f a (x:xs) | f a x = [a,x] ++ xs
                  | True  = [x] ++ (insert a xs)
