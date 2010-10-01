{-| Module      :  Similarity
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
	Check whether identifiers look alike. Identifiers are alike if:
	- they are the same when compared insensitive w.r.t. case
	- they differ in one character (filter and fi1ter)
	- one has a character more than the other (concatMap and concattMap)
	- two characters are swapped (filtre and filter)
-}

module Similarity(similar) where

import Char
import Utils(internalError)

similar :: String -> String -> Bool
-- ignore primitives
similar ('$':c:_) _  | isAlpha c  = False
similar _ ('$':c:_)  | isAlpha c  = False
-- normal test
similar name1' name2' =
    name1 == name2
    ||
    oneDiff name1 name2
    || 
    oneMore name1 name2
    ||
    oneMore name2 name1
    || 
    name1 `elem` swap name2
    where
        name1 = map toUpper name1'
        name2 = map toUpper name2'

oneMore :: String -> String -> Bool
oneMore xs ys = 
    length xs - length ys == 1
    &&
    or (map (== ys) (dropOne xs))

dropOne :: String -> [String]
dropOne []     = []
dropOne (x:xs) = xs : map (x:) (dropOne xs)

oneDiff :: String -> String -> Bool
oneDiff xs ys = 
    length xs == length ys
    &&
    length (filter (== True) (zipWith (==) xs ys)) == length xs - 1

swap :: [a] -> [[a]]
swap [_] = []
swap (x:y:xs) = (y:x:xs) : map (x:) (swap (y:xs))
swap [] = internalError "Similarity" "swap" "empty string"
