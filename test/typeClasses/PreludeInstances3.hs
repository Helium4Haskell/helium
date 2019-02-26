data MEither a b = MLeft a | MRight b

instance (Eq a, Eq b) => Eq (MEither a b) where
    MLeft x == MLeft y = x == y
    MRight x == MRight y = x == y
    _ == _ = False

main = [
        MLeft 3 == (MLeft 3 :: MEither Int Int), 
        MLeft 3 == (MLeft 5 :: MEither Int Int), 
        MRight 3 == (MRight 3 :: MEither Int Int), 
        MRight 3 == (MRight 5 :: MEither Int Int), 
        MLeft 3 == (MRight 3 :: MEither Int Int), 
        MLeft 3 == (MRight 5 :: MEither Int Int), 
        MRight 3 == (MLeft 3 :: MEither Int Int), 
        MRight 3 == (MLeft 5 :: MEither Int Int)
    ]

    