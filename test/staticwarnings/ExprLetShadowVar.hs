module ExprLetShadowVar where



main :: Int
main = let { x :: a; x = x main } in let { x :: Int; x = 1 } in x