type Phantom a = ()

pInt :: Phantom Int
pInt = undefined

f :: Phantom Bool -> Bool
f _ = True

main = f pInt