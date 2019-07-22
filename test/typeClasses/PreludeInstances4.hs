data MMaybe a = MJust a | MNothing

instance Eq a => Eq (MMaybe a) where
    MNothing == MNothing = False
    MJust x == MJust y = x == y
    _ == _ = False
 
instance Ord a => Ord (MMaybe a) where
    _ < MNothing = False
    MJust x < MJust y = x < y
    _ < MJust _ = True

main = [
        [
            MJust 1 < MJust 1 ,
            MJust 1 < MJust 2 ,
            MJust 2 < MJust 1 ,
            MNothing < MJust 1 ,
            MNothing < MJust 2 ,
            MNothing < MJust 1 ,
            MJust 1 < MNothing ,
            MJust 1 < MNothing ,
            MJust 2 < MNothing ,
            MNothing < (MNothing :: MMaybe Int),
            MNothing < (MNothing :: MMaybe Int) ,
            MNothing < (MNothing :: MMaybe Int)
        ],
        [
            MJust 1 <= MJust 1 ,
            MJust 1 <= MJust 2 ,
            MJust 2 <= MJust 1 ,
            MNothing <= MJust 1 ,
            MNothing <= MJust 2 ,
            MNothing <= MJust 1 ,
            MJust 1 <= MNothing ,
            MJust 1 <= MNothing ,
            MJust 2 <= MNothing ,
            MNothing <= (MNothing :: MMaybe Int),
            MNothing <= (MNothing :: MMaybe Int) ,
            MNothing <= (MNothing :: MMaybe Int)
        ],
        [
            MJust 1 > MJust 1 ,
            MJust 1 > MJust 2 ,
            MJust 2 > MJust 1 ,
            MNothing > MJust 1 ,
            MNothing > MJust 2 ,
            MNothing > MJust 1 ,
            MJust 1 > MNothing ,
            MJust 1 > MNothing ,
            MJust 2 > MNothing ,
            MNothing > (MNothing :: MMaybe Int),
            MNothing > (MNothing :: MMaybe Int) ,
            MNothing > (MNothing :: MMaybe Int)
        ],
        [
            MJust 1 >= MJust 1 ,
            MJust 1 >= MJust 2 ,
            MJust 2 >= MJust 1 ,
            MNothing >= MJust 1 ,
            MNothing >= MJust 2 ,
            MNothing >= MJust 1 ,
            MJust 1 >= MNothing ,
            MJust 1 >= MNothing ,
            MJust 2 >= MNothing ,
            MNothing >= (MNothing :: MMaybe Int),
            MNothing >= (MNothing :: MMaybe Int) ,
            MNothing >= (MNothing :: MMaybe Int)
        ]
    ]

    