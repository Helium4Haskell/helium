-- should get an overloading warning
main = let eq = (==)
       in eq 3 4
