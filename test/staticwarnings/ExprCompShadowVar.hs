module ExprCompShadowVar where



main :: [Int]
main = [ x | x <- [1,2], x <- [3, 4] ]
