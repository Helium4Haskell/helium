module Logger ( logger ) where

import Socket   
import Concurrent
import Monad
import System
import List
import IO

---------------------------------------------------
-- Global variables and settings

loggerHOSTNAME    = {- Bastiaan     -} -- "ikaria.cs.uu.nl" 
                    {- Jurriaan     -} -- "ranum.cs.uu.nl" 
                    {- StudentenNet -} "bellatrix.students.cs.uu.nl" 
loggerPORTNUMBER  = 5010
loggerDELAY       = 50000    -- in micro-seconds
loggerRETRIES     = 1
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
            Just (imports,hsFile) -> do --error (show (hsFile:imports))
                                        let f name = do program <- readFile name                                                        
                                                        return (  snd (extractPath name) 
                                                               ++ "\n" 
                                                               ++ program                
                                                               ++ loggerSPLITSTRING 
                                                               )
                                            nrOfFiles = show (1 + length imports)
                                        xs <- mapM f imports
                                        x  <- f hsFile
                                        return (concat (loggerSPLITSTRING:x:xs))
                             
                                              `catch` (\exception -> return (loggerNOPROGRAMS) )
                         
      sendLogString (username++":"++logcode++sources)

sendLogString :: String -> IO ()
sendLogString message = withSocketsDo (rec 0)
 
 where
  rec i = do sendToAndFlush loggerHOSTNAME (PortNumber loggerPORTNUMBER) message
             debug "The log-information was successfully sent"
          `catch`       
              \exception -> 

                 if i+1 >= loggerRETRIES 

                   then debug "Could not make a connection: stopping"

                   else do debug "Could not make a connection: sleeping"
                           threadDelay loggerDELAY
                           rec (i+1)
                
  debug :: String -> IO ()
  debug s = when loggerDEBUGMODE (putStrLn s)

{- from Utils.hs.....because of the import-dependencies, it is not possible to import 
   this function directly -}
   
-- extractPath "dir\dir2\test" -> ("dir\dir2", "test")
-- extractPath "test" -> (".", "test")
-- supports both windows and unix (and even mixed!) paths
extractPath :: String -> (String,String)
extractPath filePath =
    case (lastIndexOf '\\' filePath, lastIndexOf '/' filePath) of 
        (Nothing, Nothing) -> (".", filePath)
        (Nothing, Just i ) -> (take i filePath, drop (i+1) filePath)
        (Just i , Nothing) -> (take i filePath, drop (i+1) filePath)
        (Just i , Just j )
            | i >= j       -> (take i filePath, drop (i+1) filePath)
            | otherwise    -> (take j filePath, drop (j+1) filePath)
            
   where {--- Returns the index of the last occurrence of the given element in the given list -}
     lastIndexOf :: Eq a => a -> [a] -> Maybe Int
     lastIndexOf x xs =
        case elemIndex x (reverse xs) of       
            Nothing     ->  Nothing
            Just idx    ->  Just (length xs - idx - 1)            

{-
sendToAndFlush :: Hostname      -- Hostname
               -> PortID        -- Port Number
               -> String        -- Message to send
               -> IO ()
-}               
sendToAndFlush h p msg = do
  s <- connectTo h p
  hPutStr s msg
  hFlush s
  hClose s
