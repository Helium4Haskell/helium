elem :: Int -> [Int] -> Bool 
elem x xs = [y | y<-xs, y==x] /= []
