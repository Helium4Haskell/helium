module PMC9 where

main :: Bool
main = null2 [1,2,3]

null2 :: [a] -> Bool
null2 []    = True
null2 (_:_) = False
