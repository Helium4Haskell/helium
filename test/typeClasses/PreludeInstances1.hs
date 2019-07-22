data X = X Int

instance Eq X where
    (X x) == (X y) = x <= y

main = [
            X 3 == X 2
        ,   X 3 == X 3
        ,   X 3 == X 4
        ,   X 3 == X 5
    ]
    