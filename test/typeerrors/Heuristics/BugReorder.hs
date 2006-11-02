data A = A [A]

f :: A -> [String]
f = undefined

g :: A -> [[String]]
g (A ps) = [f (A ps)]
g (A ps) = f (A ps)
g _      = f undefined