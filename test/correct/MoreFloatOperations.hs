module MoreFloatOperations where

main :: ([Float], [Int])
main = 
    (   [ 3.4 **. 3.8
        , sqrt 45.2
        , exp 3.7
        , log 100.5 
        , sin 3.15
        , cos 12.8
        , tan 9.4
        , intToFloat 4
        ]
    ,   [ ceiling 3.7
        , ceiling 3.3
        , floor 3.7
        , floor 3.3
        , round 3.7
        , round 3.3
        , truncate 3.7
        , truncate 3.3
        , ceiling (-.5.7)
        , ceiling (-.5.3)
        , floor (-.5.7)
        , floor (-.5.3)
        , round (-.5.7)
        , round (-.5.3)
        , truncate (-.5.7)
        , truncate (-.5.3)
        , round 0.5
        , round 1.5
        , round 2.5
        , round 3.5
        ]
    )
{-Hugs
intToFloat :: Int -> Float    
intToFloat = fromInt
-}
-- Hugs & Helium
-- ([104.621,6.72309,40.4473,4.61016,-0.00840734,0.972833,-0.0247834,4.0],
-- ([104.621,6.72309,40.4473,4.61016,-0.00840725,0.972833,-0.024783,4],

--           x                    x
--  [4,4,3,3,4,3,3,3,-5,-5,-6,-6,-6,-5,-5,-5])
--  [4,4,3,3,4,3,3,3,-5,-5,-6,-6,-6,-5,-5,-5])

