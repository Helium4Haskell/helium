module Qual9( module Qual1, hello ) where

import qualified Qual1 as Q (listtest)

{-
data Listt3 a = a :>>< (Listt3 a) 
              | Emptyy
-}       
listtest :: String
listtest = "Hello! This should be sensible text"

hello :: String
hello = listtest

main :: String
main = hello