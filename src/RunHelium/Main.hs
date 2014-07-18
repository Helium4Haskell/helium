{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The wrapper for running lvmrun (for a particular installation of helium)
       
-}

module Main where

import Data.Char
import Data.Maybe(fromJust)
import Data.List(isPrefixOf, intercalate)

import System.Environment(getArgs)
import System.Process(system)
import System.Exit(exitWith, ExitCode(..))
import Utils.OSSpecific(slash)
import TextHint.ConfigFile(Config, readConfig)
import Main.Args
import Paths_helium

-- Constants for configuration files
configFilename :: String
configFilename = "hint.conf" 
temppathKey    :: String
temppathKey    = "temppath"
unknown        :: String
unknown        = "<unknown>"
passToHelium   :: [String]
passToHelium   = ["overloadingon", "loggingon", "host", "port",
                  "lvmpaths", "additionalheliumparameters"]

data State = 
    State
    { maybeModName   :: Maybe String
    , maybeFileName  :: Maybe String
    , tempDir :: String
    , compOptions :: [String] -- Contains both options for helium as well as lvmrun. 
            -- For lvmrun only the -P/--lvmpath options are selected to be passed on 
    }

unwordsBy :: String -> [String] -> String
unwordsBy _   [] = ""
unwordsBy _   [w] = w
unwordsBy sep (w:ws) = w ++ sep ++ unwordsBy sep ws

extractOptions :: Config -> [String]
extractOptions []         = []
extractOptions ((k,v):xs) = 
  if k `elem` passToHelium then
      tfm k : rest
  else
      rest
   where
     rest = extractOptions xs
     tfm x = case x of 
               "overloadingon" -> if v == "false" then
                                    show NoOverloading
                                  else
                                    show Overloading
               "loggingon"     -> if v == "false" then
                                    show DisableLogging
                                  else
                                    show EnableLogging
               "host"          -> show (Host v)
               "port"          -> show (Port (read v))
               "lvmpaths"      -> if trim v == "" then "" else show (LvmPath v)
               "additionalheliumparameters" -> v
               _               -> error "Internal error in RunHelium/Main.hs"


slashify :: String -> String
slashify xs = if last xs == slash then xs else xs ++ [slash]

main :: IO ()
main = do
    -- Read all configuration info first
    configFullname <- getDataFileName configFilename
    configInfo <-
        readConfig configFullname
    let tempDirFromEnv = case lookup temppathKey configInfo of
                           Nothing -> "."
                           Just xs -> xs
    let configOptions  = extractOptions configInfo
    
    -- Load command-line parameter module
    -- If the final parameter happens to refer to a source name, then that file is loaded.
    args <- getArgs
    
    -- Delete empty option strings since they screw things up
    (options, lvmFilename) <- processRunHeliumArgs ((filter (/= "") configOptions) ++ args) -- args take precedence over config file
    
    -- We can now assume the options are correct, and if maybeFileName is a Just, then we load this as file.
    -- This might fail as an ordinary load might. 

    baseLibs <- if overloadingFromOptions options 
                then getDataFileName "lib/" 
                else getDataFileName "lib/simple/" -- Where the base libs are.

    let initialState = 
         State { tempDir = slashify tempDirFromEnv
               , maybeModName = Nothing
               , maybeFileName = Nothing        
               , compOptions = ["-P"++baseLibs] -- Only -P is needed for lvmrun
               }                     

    -- Enter read-eval-print loop
    executeModule (fromJust lvmFilename) initialState

    return ()

executeModule :: String -> State -> IO ()
executeModule fileName state = do
    let invocation = "\"" ++ "lvmrun\" " ++ (intercalate " " (compOptions state)) ++ " \""++ fileName ++ "\""
    putStrLn invocation
    _ <- sys invocation
    return ()
    
sys :: String -> IO ExitCode
sys s = do
    -- putStrLn ("System:" ++ s)
    system s

------------------------
-- Utility functions 
------------------------

fatal :: String -> IO a
fatal msg = do    
    putStrLn msg
    putStrLn "Make sure that the environment variable TEMP points to a valid directory"
    exitWith (ExitFailure 1)

safeTail :: [a] -> [a]
safeTail (_:xs) = xs
safeTail [] = []

contains :: Eq a => [a] -> [a] -> Bool
_  `contains` [] = True
[] `contains` _  = False
(large@(_:rest)) `contains` small = 
    small `isPrefixOf` large || rest `contains` small 

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- Split file name
-- e.g. /docs/haskell/Hello.hs =>
--   filePath = /docs/haskell  baseName = Hello  ext = hs
splitFilePath :: String -> (String, String, String)
splitFilePath filePath = 
    let slashes = "\\/"
        (revFileName, revPath) = span (`notElem` slashes) (reverse filePath)
        (baseName, ext)  = span (/= '.') (reverse revFileName)
    in (reverse revPath, baseName, dropWhile (== '.') ext)

