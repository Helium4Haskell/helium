module File3 where

main :: IO ()
main
  = do s1 <- readFile "correct/File3.hs" 
       writeFile "correct/File3.temp" s1
       s2 <- readFile "correct/File3.temp"
       if (eqString s1 s2)
        then putStrLn "The read and writes are equal!"
        else putStrLn "*** ERROR: The read and writes are not equal?"
