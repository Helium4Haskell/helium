module TypeConInExpr where

data MyTree a b = Bin (MyTree a b) a (MyTree a b)
                | Leaf b

main = if Bool then "aap" else "aapje"

match (MyTree a b) = a

fout = Maybe 5
