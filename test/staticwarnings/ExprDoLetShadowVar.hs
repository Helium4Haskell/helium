module ExprDoLetShadowVar where



main :: Int
main = unsafePerformIO main_

main_ :: IO Int
main_ = do { let { x :: a; x = x main } ; let { x :: Int; x = 1 } ; return x}