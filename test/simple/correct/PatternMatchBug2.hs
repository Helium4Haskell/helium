module PatternMatchBug2 where

main :: String
main = 
    case ["a", "a"] of
        ["a", x] -> x
   