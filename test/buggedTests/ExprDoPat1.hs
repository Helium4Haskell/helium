module ExprDoPat1 where

main :: Int
main = unsafePerformIO (
    do
        (x:_) <- return [1, 2, 3]
        return x
    )