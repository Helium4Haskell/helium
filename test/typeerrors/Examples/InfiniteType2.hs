module InfiniteType2 where

voegIn :: Int -> [Int] -> [Int]
voegIn x [] = [x]
voegIn x (y:ys) | x<=y = x:y:ys
                | True = y:(voegIn x ys)

insertionSort :: [Int] -> [Int]
insertionSort xs = insertionSort' [] xs

insertionSort' :: [Int] -> [Int] -> [Int]
insertionSort' ys [] = ys
insertionSort' ys (x:xs) = insertionSort' (voegIn x ys) xs

--merge :: ([a] -> [b]) -> [ab]
merge [] = [] 
merge [xs:xss] = xs insertionSort xss
