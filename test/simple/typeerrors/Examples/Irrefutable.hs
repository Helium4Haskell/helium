module Irrefutable where

main = (f True (3,4), f False undefined)

f :: Bool -> (Int, Int) -> Int
f lookInside ~(True, y) = if lookInside then 1 else 0

