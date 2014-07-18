{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The wrapper for running lvmrun (for a particular installation of helium)
       
-}

module Main where

import Data.Maybe(fromJust)
import Data.List(intercalate)

import System.Environment(getArgs)
import System.Process(system)
import System.Exit(ExitCode(..))
import Utils.OSSpecific(slash)
import TextHint.ConfigFile(readConfig, extractOptions, configFilename, 
                           temppathKey)
import Main.Args
import Paths_helium

data State = 
    State
    { maybeModName   :: Maybe String
    , maybeFileName  :: Maybe String
    , tempDir :: String
    , compOptions :: [String] -- Contains both options for helium as well as lvmrun. 
            -- For lvmrun only the -P/--lvmpath options are selected to be passed on 
    }

    
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
    _ <- sys invocation
    return ()

-- Local sys in case we want to impose additional side effects
sys :: String -> IO ExitCode
sys s = do
    -- putStrLn ("System:" ++ s)
    system s

