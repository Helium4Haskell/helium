module ShowFunctions where

main :: IO ()
main = putStr $ unlines 
    [ show (-412)
    , show 0
    , show 34
    , show 1000
    , show ' '
    , show '\n'
    , show 'A'
    , show True
    , show False
    , show ()
    , show (1,2)
    , show (1,2,3)
    , show (1,2,3,4)
    , show (1,2,3,4,5)
    , show (1,2,3,4,5,6)
    , show (1,2,3,4,5,6,7)
    , show (1,2,3,4,5,6,7,8)
    , show (1,2,3,4,5,6,7,8,9)
    , show (1,2,3,4,5,6,7,8,9,10)
    , showFunction showInt showInt id
    , showIO showChar getChar
    , showString "hello"
    , showString ""
    , showString "abc\ndef"
    , show [1..10]
    , show [5]
    , show []
    ]
    
