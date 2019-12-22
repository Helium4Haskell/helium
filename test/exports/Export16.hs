module Export16 where

import ExportBasic5

correct :: Bool
correct = r1 && r2 && r4 == 5 && r5 r3
    where
        r1 = f == 4
        r2 = 1 /** 1 /** 1 == 18
        
        r3 :: Listt5 Int
        r3 = 5 :> 5
        
        r4 :: Hello2
        r4 = 5
        
        r5 :: Listt5 a -> Bool
        r5 Empty = False
        r5 _     = True

main :: Bool
main = correct