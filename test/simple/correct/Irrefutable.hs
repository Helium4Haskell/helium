module Irrefutable where

main = (f True (3,4), f False undefined)

f :: Bool -> (Int, Int) -> Int
f lookInside ~(x, y) = if lookInside then x else 0

