module PMC16 where

main :: Bool
main = not2 False

not2 :: Bool -> Bool
not2 True = False
not2 _    = True
