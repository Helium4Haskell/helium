module Sieve where

main = take 3000 (sieve [2..])

sieve (x:xs) 
   = x 
   : sieve (filter (nietVeelvoud x) xs)

nietVeelvoud x y = y `mod` x /= 0
    
{-
[/cygdrive/c/docs/helium/helium/demo] time heliumc Sieve.hs
Compiling Sieve.hs
(3,1): Missing type signature: main :: [Int]
(5,1): Missing type signature: sieve :: [Int] -> [Int]
(9,1): Missing type signature: nietVeelvoud :: Int -> Int -> Bool
Compilation succesful with 3 warnings

real    0m2.234s
user    0m0.010s
sys     0m0.010s

real    0m10.685s
user    0m0.010s
sys     0m0.010s
[/cygdrive/c/docs/helium/helium/demo] time lvmrun Sieve

LVMfile 13676 bytes

-- Splitsing HeliumLang en PreludePrim

[/cygdrive/c/docs/helium/helium/demo] time heliumc -b Sieve.hs
Compiling Sieve.hs
(3,1): Missing type signature: main :: [Int]
(5,1): Missing type signature: sieve :: [Int] -> [Int]
(9,1): Missing type signature: nietVeelvoud :: Int -> Int -> Bool
Compilation succesful with 3 warnings

real    0m1.653s
user    0m0.010s
sys     0m0.010s

LVMfile 11.724 bytes


[/cygdrive/c/docs/helium/helium/demo] time heliumc -b Sieve.hs
Compiling Sieve.hs
(3,1): Missing type signature: main :: [Int]
(5,1): Missing type signature: sieve :: [Int] -> [Int]
(9,1): Missing type signature: nietVeelvoud :: Int -> Int -> Bool
Compilation succesful with 3 warnings

real    0m1.672s
user    0m0.010s
sys     0m0.010s


real    0m10.165s

real    9.644s !
-}
