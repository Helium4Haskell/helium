data A  = A Int
        | B Char
    deriving (Eq, Show)
    
main = (A 3 == A 3, show (B 'q'))
