module Sections where

data Expr 
    = Num Int
    | Expr :+: Expr
    | (:-) Int
    
main = 
    (   [   (+1) 2
        ,   (+(-3)) 2
        ,   (+(-1)) 3
        ,   (+(3*2)) 7
        ,   (1+) 2
        ,   (3-) 2
        ,   (1-) 3
        ,   ((3*2)+) 7
        ,   (20 `mod`) 3
        ,   (`mod` 4) 51
        ]
        ++
        map (2*) [1..10]
        ++
        map (*2) [1..10]
    ,   [   (:+: Num 3) (Num 4 :+: Num 5)
        ,   (Num 4 :+:) (Num 6)
        ,   (:-) 4
        ]
    ,   [   (++"val") "water"
        ,   ("ape"++) "staart"
        ,   (:[]) 'b'
        ]
    )
    