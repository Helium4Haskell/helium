module TypeBug4 where

sp :: ([a] -> Int -> String) -> [a] -> String
sp k l | length k < max length k (max.map(length l)) = k : sp k : " "
       | True                                        = k


