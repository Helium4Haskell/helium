main = 
  ( (3 == 4 == 5) == 6 /= 7
  , 3 ++< 5 ++> 6
  , 3 ++< 5 == 6
  )

(++<) :: Int -> Int -> Int
(++<) x y = x

(++>) :: Int -> Int -> Int
(++>) x y = x

infixl 4 ++<
infixr 4 ++>
