module TypeBug7 where

main (x,y,z) = f(concat(g(special z)))
    where f (a:as) = a : "|" : f as
          g [a] = [head a : "\n" : g (tail a)]
          
special :: [[String]] -> [[String]]
special = undefined          
