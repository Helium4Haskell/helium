data A = A Int
       | B Char

data D = E deriving Eq

main = A 3 == B 'a'
