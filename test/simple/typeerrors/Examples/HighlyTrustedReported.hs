import List

f lijst table 
   | elemBy eqString (head(head(transpose table))) lijst  = 
        head(transpose table) ++ f lijst transpose(tail(transpose table))
   | otherwise = 
        f lijst transpose(tail(transpose table))

