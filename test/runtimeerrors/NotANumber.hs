module NotANumber where

abcFormule' :: Float -> Float -> Float -> [Float]
abcFormule' a b c = [ (-.b+.d)/.n,(-.b-.d)/.n]
   where d :: Float
         d = sqrt (b*.b-.4.0*.a*.c)
         n :: Float
         n = 2.0*.a
         
main :: [Float]         
main = abcFormule' 1.0 1.0 1.0
