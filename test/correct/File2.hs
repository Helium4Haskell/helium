module File2 where

main :: IO ()
main
  = do s <- readFile "File2.hs" 
       hPutString stdout s

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
