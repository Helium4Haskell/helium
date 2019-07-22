data X = X Int

instance Eq X where
    (X x) == (X y) = x <= y

main = [
        [X 3, X 5, X 7] == [X 3, X 5, X 7]
    ,   [X 2, X 4, X 6] == [X 3, X 5, X 7]
    ,   [X 6, X 4, X 6] == [X 3, X 5, X 7]
    ,   [X 2, X 4, X 6] == [X 3, X 5, X 7]
    ]   


    