module AppSwap2 where

type IntTable a = [(Int,a)]

zeroValue :: String
zeroValue = dictionary ? 0

(?) :: Int -> IntTable b -> b
(?) = undefined

dictionary :: IntTable String
dictionary = [ (0,"nul"), (1,"een"), (2,"twee") ]
