module File3 where

main :: IO ()
main
  = do s1 <- readFile "File3.hs" 
       writeFile "File3.temp" s1
       s2 <- readFile "File3.temp"
       if (eqString s1 s2)
        then putStrLn "The read and writes are equal!"
        else putStrLn "*** ERROR: The read and writes are not equal?"

writeFile fname s
  = bracket (openFile fname WriteMode)
            (hClose)
            (\h -> hPutString h s)

readFile fname
  = bracket (openFile fname ReadMode)
            (hClose)
            (\h -> readAll h [])
  where
    readAll h acc 
      = do c  <- hGetChar h
           readAll h (c:acc) 
        `catchEof` (return (reverse acc))

bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracket acquire release action
  = do x <- acquire
       finally (action x) (release x)

finally :: IO a -> IO b -> IO a
finally io action
  = do x <- io `catch` (\exn -> do{ action; raise exn })
       action
       return x
