data A = A (Int -> Int)
   deriving Show

main = show (A id)
