module Logger ( logger ) where

import Socket   
import Concurrent
--import Posix
import Monad
import System
import List
import IO
import Version

---------------------------------------------------
-- Global variables and settings

loggerHOSTNAME    = {- Bastiaan     -} -- "ikaria.cs.uu.nl" 
                    {- Jurriaan     -} -- "ranum.cs.uu.nl" 
                    {- StudentenNet -} "bellatrix.students.cs.uu.nl" 
loggerPORTNUMBER  = 5010
loggerDELAY       = 50000    -- in micro-seconds
loggerRETRIES     = 5
loggerSPLITSTRING = "\n\NUL\n"
loggerNOPROGRAMS  = "\n\SOH\n"
loggerDEBUGMODE   = False
loggerENABLED     = True
loggerUSERNAME    = "USERNAME"

------------------------------------------------------
-- The function to send a message to a socket

logger :: String -> Maybe ([String],String) -> IO ()
logger logcode maybeSources | not loggerENABLED = return ()
                            | otherwise      = 
                            
   do username <- (getEnv loggerUSERNAME) `catch` (\exception -> return "unknown")
      sources  <- case maybeSources of 
            Nothing               -> return (loggerNOPROGRAMS)
            Just (imports,hsFile) -> 
               let f name = do program <- readFile name                                                        
                               return (  baseNameOf name
                                      ++ "\n" 
                                      ++ program                
                                      ++ loggerSPLITSTRING 
                                      )
                   nrOfFiles = show (1 + length imports)
               in 
                  do xs <- mapM f imports
                     x  <- f hsFile
                     return (concat (loggerSPLITSTRING:x:xs))
               
                       `catch` (\exception -> return (loggerNOPROGRAMS) )
                         
      sendLogString (username++":"++logcode++":"++version++sources)

sendLogString :: String -> IO ()
sendLogString message = withSocketsDo (rec 0)
 
 where
  rec i = do --installHandler sigPIPE Ignore Nothing
             handle <- connectTo loggerHOSTNAME (PortNumber loggerPORTNUMBER)
             hSetBuffering handle (BlockBuffering (Just 1024))
             sendToAndFlush handle message
          `catch`       
              \exception -> 
                 if i+1 >= loggerRETRIES 
                   then debug "Could not make a connection: no send"
                   else do debug "Could not make a connection: sleeping"
                           threadDelay loggerDELAY
                           rec (i+1)
                
  debug :: String -> IO ()
  debug s = when loggerDEBUGMODE (putStrLn s)

{- from Utils.hs.....because of the import-dependencies, it is not possible to import 
   this function directly -}

splitFilePath :: String -> (String, String, String)
splitFilePath filePath = 
    let slashes = "\\/"
        (revFileName, revPath) = span (`notElem` slashes) (reverse filePath)
        (revExt, revBaseName)  = span (/= '.') revFileName
    in (reverse revPath, reverse (dropWhile (== '.') revBaseName), reverse revExt)

baseNameOf :: String -> String
baseNameOf fullName = let (_, baseName, _) = splitFilePath fullName in baseName

{-
sendToAndFlush :: Hostname      -- Hostname
               -> PortID        -- Port Number
               -> String        -- Message to send
               -> IO ()
-}               
sendToAndFlush handle msg = do  
  hPutStr handle msg
  hPutStr handle loggerSPLITSTRING
  hFlush handle
--  b1 <- hIsWritable s
--  b2 <- hIsReadable s
--  putStrLn ((if b1 then "writable" else "not writable") ++ " and " ++ 
--      (if b2 then "readable" else "not readable"))
  debug "Waiting for a handshake"  
  handshake <- getRetriedLine 0
  debug ("Received a handshake: " ++ show handshake)
--  hClose handle
  where
    getRetriedLine i = 
      do
        line <- hGetLine handle
        return line
      `catch`
        \exception -> 
          if i+1 >= loggerRETRIES 
            then do
                   debug "Did not receive anything back"
                   return ""
            else do 
                   debug "Waiting to try again"
                   threadDelay loggerDELAY
                   getRetriedLine (i+1)    
    debug :: String -> IO ()
    debug s = when loggerDEBUGMODE (putStrLn s)

