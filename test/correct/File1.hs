module File1 where

main :: IO ()
main
  = do h <- openFile "File1.hs" ReadMode
       c <- hGetChar h 
       hPutChar stdout c
           