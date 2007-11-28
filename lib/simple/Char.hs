module Char where

isSpace :: Char -> Bool
isSpace c =
    i == ord ' '  || i == ord '\t' || i == ord '\n' ||
    i == ord '\r' || i == ord '\f' || i == ord '\v'
  where
    i = ord c
        
isUpper :: Char -> Bool
isUpper c = ord c >= ord 'A' && ord c <= ord 'Z' 

isLower :: Char -> Bool
isLower c = ord c >= ord 'a' && ord c <= ord 'z'

isDigit :: Char -> Bool
isDigit c = ord c >= ord '0' && ord c <= ord '9'

isAlpha :: Char -> Bool
isAlpha c = isUpper c || isLower c

isAlphaNum :: Char -> Bool
isAlphaNum c =  isAlpha c || isDigit c

toUpper :: Char -> Char
toUpper c
    | isLower c = chr ( ord c - ord 'a' + ord 'A' )
    | otherwise = c

toLower :: Char -> Char
toLower c
    | isUpper c = chr ( ord c - ord 'A' + ord 'a' )
    | otherwise = c
