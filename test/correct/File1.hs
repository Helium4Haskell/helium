module File1 where

main :: IO ()
main
  = do h <- openFile "correct/File1.hs" ReadMode
       c <- hGetChar h 
       hPutChar stdout c
           