{-| Module      :  Logger
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Utils.Logger ( logger, logInternalError ) where

import Network
import Control.Concurrent

import Control.Monad
import System.Environment
import Data.Char
import Data.Maybe
import Data.List
import Main.Args
import System.IO
import Main.Version


{-# NOTINLINE logger #-}

---------------------------------------------------
-- Global variables and settings
-- Some additional ones are in Args.hs

loggerDELAY, loggerTRIES :: Int
loggerDELAY       = 10000    -- in micro-seconds
loggerTRIES       = 2

loggerINTERNALERRORHOSTNAME :: String
loggerINTERNALERRORHOSTNAME = "helium.zoo.cs.uu.nl"
loggerINTERNALERRORPORTNR   :: Int
loggerINTERNALERRORPORTNR   = loggerDEFAULTPORT

loggerSEPARATOR, loggerTERMINATOR, loggerUSERNAME, loggerDEFAULTNAME :: String
loggerSEPARATOR      = "\NUL\NUL\n"
loggerTERMINATOR     = "\SOH\SOH\n"
loggerUSERNAME       = "USERNAME"
loggerDEFAULTNAME    = "unknown"

loggerADMINSEPARATOR, escapeChar :: Char
loggerADMINSEPARATOR = '|'
escapeChar     = '\\'

loggerESCAPABLES :: String
loggerESCAPABLES     = [loggerADMINSEPARATOR, escapeChar]

alertESCAPABLES :: String
alertESCAPABLES     = "\""

debug :: String -> Bool -> IO ()
debug s loggerDEBUGMODE = when loggerDEBUGMODE (putStrLn s)

-- Make sure that options that contain a space are quoted with double quotes.
-- And all double quotes in the options are escaped.
unwordsQuoted :: [String] -> String
unwordsQuoted words = unwords (map (quote . escape alertESCAPABLES) words)
 where
   quote s = if ' ' `elem` s then "\"" ++ s ++ "\"" else s -- Not efficient, but balanced.

------------------------------------------------------
-- Normalization/escaping functions

normalizeName :: String -> String
normalizeName name = let 
                       newname = map toLower (filter isAlphaNum name)
                     in   
                       if null newname then loggerDEFAULTNAME else newname

-- Escapes all characters from the list escapables
escape :: String -> String -> String
escape _          []     = []
escape escapables (x:xs) = 
    if x `elem` escapables
      then escapeChar : rest 
      else rest
    where 
      rest = x : escape escapables xs

-- Remove line breaks and escape special characters                
normalize :: String -> String
normalize = escape loggerESCAPABLES . filter ('\n' /=)

logInternalError :: Maybe ([String],String) -> IO ()
logInternalError maybeSources = 
  logger "I" maybeSources internalErrorOptions
    where
      internalErrorOptions = [EnableLogging, Host loggerINTERNALERRORHOSTNAME, Port loggerINTERNALERRORPORTNR]

------------------------------------------------------
-- The function to send a message to a socket
-- TODO : decide whether we really don't want to send interpreter input.

logger :: String -> Maybe ([String],String) -> [Option] -> IO ()
logger logcode maybeSources options =
   let
     debugLogger = DebugLogger `elem` options
     reallyLog   = EnableLogging `elem` options -- We use that the presence of an alert adds EnableLogging in Options.hs
     hostName    = fromMaybe loggerDEFAULTHOST (hostFromOptions options)
     portNumber  = fromMaybe loggerDEFAULTPORT (portFromOptions options)
   in
     if reallyLog then
       do
         debug (hostName ++ ":" ++ show portNumber) debugLogger
         username     <- getEnv loggerUSERNAME `catch` (\_ -> return loggerDEFAULTNAME)
         optionString <- getArgs
         sources      <- case maybeSources of 
             Nothing -> 
                 return loggerTERMINATOR
             Just (imports,hsFile) -> 
                 do let allHsFiles = hsFile:imports
                        allFiles   = allHsFiles ++ map toTypeFile allHsFiles
                    xs <- mapM (getContentOfFile debugLogger) allFiles
                    return (concat (loggerSEPARATOR:xs)++loggerTERMINATOR) 
                      `catch` (\_ -> return loggerTERMINATOR)
         {- putStr (normalizeName username ++ 
                        (loggerADMINSEPARATOR : normalize logcode) ++ 
                        (loggerADMINSEPARATOR : normalize version) ++
                        (loggerADMINSEPARATOR : normalize (unwords optionString)) ++ 
                        "\n" ++sources) -}      
         let alertLogcode = if hasAlertOption options then map toLower logcode else map toUpper logcode
         sendLogString hostName
                       portNumber
                       (normalizeName username ++ 
                        (loggerADMINSEPARATOR : normalize alertLogcode) ++ 
                        (loggerADMINSEPARATOR : normalize version) ++
                        (loggerADMINSEPARATOR : normalize (unwordsQuoted optionString)) ++ 
                        "\n" ++sources
                       ) 
                       debugLogger
     else                  
       return ()

toTypeFile :: String -> String
toTypeFile fullName = fullNameNoExt ++ ".type"
 where
   (path, baseName, _) = splitFilePath fullName
   fullNameNoExt       = combinePathAndFile path baseName     
                     
getContentOfFile :: Bool -> String -> IO String
getContentOfFile loggerDEBUGMODE name =    
   do program <- readFile name                                                        
      debug ("Logging file " ++ name) loggerDEBUGMODE
      return (  fileNameWithoutPath name
             ++ "\n" 
             ++ program
             ++ "\n"                
             ++ loggerSEPARATOR 
             )
 `catch`
    (\_ -> return "")
    
-- isInterpreterModule :: Maybe ([String],String) -> Bool
-- isInterpreterModule Nothing = False
-- isInterpreterModule (Just (_, hsFile)) = fileNameWithoutPath hsFile == "Interpreter.hs"

sendLogString :: String -> Int -> String -> Bool -> IO ()
sendLogString hostName portNr message loggerDEBUGMODE = withSocketsDo (rec_ 0)
 where
    rec_ i = do --installHandler sigPIPE Ignore Nothing
             handle <- connectTo hostName (PortNumber (fromIntegral portNr))
             hSetBuffering handle (BlockBuffering (Just 1024))
             sendToAndFlush handle message loggerDEBUGMODE
           `catch`       
              \exception -> 
                 if i+1 >= loggerTRIES 
                   then debug ( "Could not make a connection: no send (" ++ show exception ++ ")" ) loggerDEBUGMODE
                   else do debug ( "Could not make a connection: sleeping (" ++ show exception ++ ")" ) loggerDEBUGMODE
                           threadDelay loggerDELAY
                           rec_ (i+1)
                
{- from Utils.hs.....because of the import-dependencies, it is not possible to import 
   this function directly -}
splitFilePath :: String -> (String, String, String)
splitFilePath filePath = 
    let slashes = "\\/"
        (revFileName, revPath) = span (`notElem` slashes) (reverse filePath)
        (baseName, ext)  = span (/= '.') (reverse revFileName)
    in (reverse revPath, baseName, dropWhile (== '.') ext)
    
combinePathAndFile :: String -> String -> String
combinePathAndFile path file =
    case path of 
        "" -> file
        _  | last path == '/' -> path ++ file
           | otherwise        -> path ++ "/" ++ file
        
fileNameWithoutPath :: String -> String
fileNameWithoutPath filePath = 
    let slashes = "\\/"
        (revFileName, _) = span (`notElem` slashes) (reverse filePath)
    in reverse revFileName

sendToAndFlush :: Handle        -- Hostname
               -> String        -- Message to send
               -> Bool          -- Debug logger?
               -> IO ()               
sendToAndFlush handle msg loggerDEBUGMODE = do  
  hPutStr handle msg
  hPutStr handle loggerSEPARATOR
  hFlush handle
--  b1 <- hIsWritable s
--  b2 <- hIsReadable s
--  putStrLn ((if b1 then "writable" else "not writable") ++ " and " ++ 
--      (if b2 then "readable" else "not readable"))
  debug "Waiting for a handshake"  loggerDEBUGMODE
  handshake <- getRetriedLine 0
  debug ("Received a handshake: " ++ show handshake) loggerDEBUGMODE
--  hClose handle
  where
    getRetriedLine i = 
      hGetLine handle
      `catch`
        \_ -> 
          if i+1 >= loggerTRIES 
            then do
                   debug "Did not receive anything back" loggerDEBUGMODE
                   return ""
            else do 
                   debug "Waiting to try again" loggerDEBUGMODE
                   threadDelay loggerDELAY
                   getRetriedLine (i+1)    
