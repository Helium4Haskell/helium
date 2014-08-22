{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The wrapper for running lvmrun (for a particular installation of helium)
       
-}

module Main where

import Data.Maybe(fromMaybe)
import System.Environment(getArgs)
import System.FilePath(joinPath, pathSeparator)
import System.Process(system)
import System.Exit
import System.Directory(findExecutable,getTemporaryDirectory)
import Helium.Main.Args
import TextHint.ConfigFile
import Paths_helium

data State = 
    State
    { maybeModName   :: Maybe String
    , maybeFileName  :: Maybe String
    , tempDir :: String
    , compOptions :: [String] -- Contains both options for helium as well as lvmrun. 
            -- For lvmrun only the -P/--lvmpath options are selected to be passed on 
    }

lvmrun :: String
lvmrun = "lvmrun"

slashify :: String -> String
slashify xs = if last xs == pathSeparator then xs else xs ++ [pathSeparator]

main :: IO ()
main = do
    canWeRun <- findExecutable lvmrun
    case canWeRun of
      Nothing -> do 
                   putStrLn "Fatal error: lvmrun cannot be found in your system PATH.\nDid you run `cabal install lvmrun` yet?"
                   exitWith (ExitFailure 1)
      Just _ -> return ()
    
    -- Read all configuration info first
    configFullname <- getDataFileName configFilename
    configInfo <-
        readConfig configFullname
    tempDirFromEnv <- case lookup temppathKey configInfo of
                           Nothing -> getTemporaryDirectory
                           Just xs -> return xs
    let configOptions  = extractOptions configInfo
    
    -- Load command-line parameter module
    -- If the final parameter happens to refer to a source name, then that file is loaded.
    args <- getArgs
    
    -- Delete empty option strings since they screw things up
    (options, srcFilename) <- processRunHeliumArgs (filter (/= "") configOptions ++ args) -- args take precedence over config file
    let (fpath,filename,_) =  splitFilePath (fromMaybe "" srcFilename)
    let lvmFilename = joinPath [fpath, filename ++ ".lvm"]
    
    -- We can now assume the options are correct, and if maybeFileName is a Just, then we load this as file.
    -- This might fail as an ordinary load might. 

    baseLibs <- getDataFileName $ 
       if overloadingFromOptions options
       then slashify "lib"
       else slashify "lib" ++ slashify "simple" -- Where the base libs are.

    let initialState = 
         State { tempDir = slashify tempDirFromEnv
               , maybeModName = Nothing
               , maybeFileName = Nothing        
               , compOptions = ["-P" ++ baseLibs] -- Only -P is needed for lvmrun
               }                     

    -- Enter read-eval-print loop
    executeModule lvmFilename initialState

    return ()

executeModule :: String -> State -> IO ()
executeModule fileName state = do
    let invocation = "\"" ++ "lvmrun\" " ++ unwords (compOptions state) ++ " "++ fileName
    _ <- sys invocation
    return ()

-- Split file name
-- e.g. /docs/haskell/Hello.hs =>
--   filePath = /docs/haskell  baseName = Hello  ext = hs
splitFilePath :: String -> (String, String, String)
splitFilePath filePath = 
    let slashes = "\\/"
        (revFileName, revPath) = span (`notElem` slashes) (reverse filePath)
        (baseName, ext)  = span (/= '.') (reverse revFileName)
    in (reverse revPath, baseName, dropWhile (== '.') ext)

-- Local sys in case we want to impose additional side effects
sys :: String -> IO ExitCode
sys = system

