type A = String

apply f a b = f a b
  
test :: A -> Bool
test c = apply (==) "" c