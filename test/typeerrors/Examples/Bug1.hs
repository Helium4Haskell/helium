type Table = [[String]]

reOrderTable :: String -> Table -> Table
reOrderTable stringy tabel = (!! x): (take x tabel) : (drop (x-1) tabel)
            where x = f stringy tabel
                  f :: String -> Table -> Int
                  f _ [] = 0
                  f stringz (t:ts) |eqString stringz (head t) = 0
                                   |otherwise = 1 + f stringz ts
