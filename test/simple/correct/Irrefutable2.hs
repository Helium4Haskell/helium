module Irrefutable2 where

main = (f True (3,4,5), f False undefined)

f :: Bool -> (Int, Int, Int) -> Int
f b ~(3, y,z) = if b then y+z else 0

