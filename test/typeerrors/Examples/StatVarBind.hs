module StatVarBind where

f m = do x <- m
         if x then m else x
