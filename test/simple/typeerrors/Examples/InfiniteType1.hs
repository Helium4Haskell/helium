module InfiniteType1 where

voegIn :: (a->a->Ordering) -> a -> [a] -> [a]

voegIn cmp n [] = [n]
voegIn cmp n (x:xs) = f ( cmp n x)
             where f LT = n : (x:xs)
                   f EQ = n : (x:xs)
                   f GT = x : voegIn n xs
