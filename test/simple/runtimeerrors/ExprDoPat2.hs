module ExprDoPat2 where

main :: Int
main = unsafePerformIO (
    do
        [x] <- return [1, 2, 3]
        return x
    )