module Fixity where

infixl 4 `B`
infixr 5 `C`
infix  3 `Mix`

data A = A A A | AInt Int
data B = B B B | BInt Int
data C = C C C | CInt Int

data Mix = Mix B C

main :: (A, B, C, Mix)
main = ( AInt 1 `A` AInt 2 `A` AInt 3    -- left by default
       , BInt 1 `B` BInt 2 `B` BInt 3    -- left
       , CInt 1 `C` CInt 2 `C` CInt 3    -- right
       , BInt 1 `B` BInt 2 `Mix` CInt 3 `C` CInt 4   -- priority
       )
