module BigTypes where

f :: ((Int,Int,Int) -> (Int,Int,Int)) -> (Int,Int,Int) -> (Int,Int,Int)
f = undefined

g :: [(Bool,Bool,Bool)] -> ([(Bool,Bool,Bool)],[(Bool,Bool,Bool)],[(Bool,Bool,Bool)]) -> Bool
g = undefined

test = [ f , g ]
