module Andres where

test1 = let f (+) = 3 + 5 in f (-)

test3 = let {f x = 5; y = 4} in - f y

test4 = do let f = return () in f

main = (test1, test3)
