module PatternMatchBug4 where

main = f ["a", "a"]

f ["a", x] = x
   