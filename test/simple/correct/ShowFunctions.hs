module ShowFunctions where

main :: IO ()
main = putStr $ unlines 
    [ showInt (-412)
    , showInt 0
    , showInt 34
    , showInt 1000
    , showChar ' '
    , showChar '\n'
    , showChar 'A'
    , showBool True
    , showBool False
    , showUnit ()
    , showTuple2 showInt showInt (1,2)
    , showTuple3 showInt showInt showInt (1,2,3)
    , showTuple4 showInt showInt showInt showInt (1,2,3,4)
    , showTuple5 showInt showInt showInt showInt showInt (1,2,3,4,5)
    , showTuple6 showInt showInt showInt showInt showInt showInt (1,2,3,4,5,6)
    , showTuple7 showInt showInt showInt showInt showInt showInt showInt (1,2,3,4,5,6,7)
    , showTuple8 showInt showInt showInt showInt showInt showInt showInt showInt (1,2,3,4,5,6,7,8)
    , showTuple9 showInt showInt showInt showInt showInt showInt showInt showInt showInt (1,2,3,4,5,6,7,8,9)
    , showTuple10 showInt showInt showInt showInt showInt showInt showInt showInt showInt showInt (1,2,3,4,5,6,7,8,9,10)
    , showFunction showInt showInt id
    , showIO showChar getChar
    , showString "hello"
    , showString ""
    , showString "abc\ndef"
    , showList showInt [1..10]
    , showList showInt [5]
    , showList showChar []
    ]
    
