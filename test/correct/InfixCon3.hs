module InfixCon3 where

data A = (:+) Int

main :: Int
main = case (:+) 3 of
    (:+) x -> x
    