module DupDerivedShow where

data A = C1
data A = C2
data A = C3

showA :: Int
showA = 3

showA :: Bool
showA = True

maftype :: A Int
maftype = undefined
