module Qual10 where

import Qual1 as Q
import Qual9 as Q (listtest, hello)

f = Q.listtest

z = Q.hello

main :: String
main = Qual10.z