module Ex2 where

f (c:cs) (i:is) = if i > 0 
                    then f cs is 
                    else (c:[2.2]) ++ f is cs
