elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy _ _ [] = False
elemBy eq x (y:ys) 
  | x `eq` y = True
  | otherwise = elemBy eq x ys
{- elem is not in the Helium-prelude
elem :: Int -> [Int] -> Bool 
elem x xs = [y | y<-xs, y==x] /= [] -}
