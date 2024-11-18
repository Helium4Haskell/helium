data A = A B
   deriving Show

data B = B
   deriving Show
   
main = show (A B)
