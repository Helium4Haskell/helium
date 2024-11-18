module File2 where

main :: IO ()
main
  = do s <- readFile "correct/File2.hs" 
       hPutString stdout s
