type A = [[String]]

f :: (String, [String]) -> ([String], A) -> [[String]]
f _ ([], [])        = []
f a (hs2,(_, xss2)) = snd a ++ f a (hs2, xss2)