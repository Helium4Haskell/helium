type P a = (Int, a)

f :: P a -> ()
f = undefined

g :: P Int -> a
g = f