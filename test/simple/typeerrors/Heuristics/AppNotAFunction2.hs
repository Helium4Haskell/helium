module AppNotAFunction2 where

main x = if even x
           then [ 1 .. x ]
           else x 3
