module Export20 where

import ExportBasic6

correct :: Bool
correct = t1 t2
    where
        t2 :: Listt6 Int
        t2 = 5 :> Empty
        
        t1 :: Listt6 Int -> Bool
        t1 (5 :> _) = True
        t1 _        = False
 
main :: Bool 
main = correct