{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The textual Helium interpreter

    TODO: 
       -Pass a .hint.conf as a parameter?
        Make sure that helium itself does not allow it, explicitly forbids its use.
        
       
-}

module Main where

import Data.Char
import Data.List(isInfixOf, isPrefixOf, isSuffixOf)
import Control.Monad
import System.IO(stdout, hFlush)

import Data.IORef       ( IORef, readIORef, newIORef, writeIORef )
import System.IO.Unsafe ( unsafePerformIO )

import System.Environment(getEnv, getArgs)
import System.Process(system)
import System.Exit(exitWith, ExitCode(..))
import Utils.OSSpecific(slash)
import System.Directory
import TextHint.ConfigFile(Config, readConfig)
import Main.Args


-- Constants for configuration files
configFilename = ".hint.conf" 
basepathKey    = "basepath"
temppathKey    = "temppath"
unknown        = "<unknown>"
passToHelium   = ["overloadingon", "loggingon", "host", "port",
                  "lvmpaths", "additionalheliumparameters"]

data State = 
    State
    { maybeModName   :: Maybe String
    , maybeFileName  :: Maybe String
    , tempDir :: String
    , binDir :: String
    , compOptions :: [String] -- Contains both options for helium as well as lvmrun. 
            -- For lvmrun only the -P/--lvmpath options are selected to be passed on 
    }

unwordsBy :: String -> [String] -> String
unwordsBy _   [] = ""
unwordsBy _   [w] = w
unwordsBy sep (w:ws) = w ++ sep ++ unwordsBy sep ws

-- The following three definitions are used to support the alert flag
-- for redoing a compilation and logging the compilation in a special way.
refToPreviousInvocation :: IORef (String, String)
refToPreviousInvocation = unsafePerformIO (newIORef ("", ""))

getPreviousInvocation :: (String, String)
getPreviousInvocation = unsafePerformIO (readIORef refToPreviousInvocation)

setPreviousInvocation :: String -> String -> IO ()
setPreviousInvocation heliumInvocation redirect =  
  writeIORef refToPreviousInvocation (heliumInvocation, redirect)

header :: String
header = unlines
    [ " _          _ _                 "
    , "| |        | (_)                   "
    , "| |__   ___| |_ _   _ _ __ ___     -- Welcome to the Helium interpreter --"
    , "| '_ \\ / _ \\ | | | | | '_ ` _ \\    ---------------------------------------"
    , "| | | |  __/ | | |_| | | | | | |   -- Type an expression to evaluate    --"
    , "|_| |_|\\___|_|_|\\__,_|_| |_| |_|   --    or a command (:? for a list)   --"
    ]

extractOptions :: Config -> [String]
extractOptions []         = []
extractOptions ((k,v):xs) = 
  if k `elem` passToHelium then
      tfm k : rest
  else
      rest
   where
     rest = extractOptions xs
     tfm k = case k of 
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
               _               -> error "Internal error in texthint/Main.hs"


slashify :: String -> String
slashify xs = if last xs == slash then xs else xs ++ [slash]

-- Adds link to the right Prelude. For that needs to verify Overloading or not.
addStandardLVMPath :: String -> [String] -> [String]
addStandardLVMPath basepath config = 
  addPreludePath basepath (show (LvmPath ".") : config)
  where
    addPreludePath bp conf 
      | bp == unknown = conf
      | otherwise     = show (LvmPath (bp ++ (slash:"lib") ++ [slash] ++  
                                      (if reallyOverloading config then "" else "simple"++[slash]))) : config
    reallyOverloading xs =
      let 
        onlyOverloadingFlags = reverse (filter (\x -> x == (show Overloading) || x == (show NoOverloading)) xs)
      in 
        case onlyOverloadingFlags of
           []     -> True
           (x:_)  -> x == show Overloading
           
main :: IO ()
main = do
    home <- getEnv "HOME" 
    configInfo <-
        readConfig (home ++ (slash : configFilename))
    let tempDirFromEnv = case lookup temppathKey configInfo of
                           Nothing -> "."
                           Just xs -> xs
    let basepath       = case lookup basepathKey configInfo of
                           Nothing -> unknown
                           Just xs -> xs
    let configOptions  = extractOptions configInfo
    -- putStrLn (show configOptions) 
    let initialState = 
         State { tempDir = slashify tempDirFromEnv
               , maybeModName = Nothing
               , maybeFileName = Nothing
               , binDir = if basepath == unknown then "" else basepath ++ (slash:"bin") ++ [slash] -- Hope for $PATH
               , compOptions = []
               }

    -- Logo
    putStrLn header
    
    -- Load command-line parameter module
    -- If the final parameter happens to refer to a source name, then that file is loaded.
    args <- getArgs
    (options, maybeFilename) <- processTexthintArgs args
    -- We can now assume the options are correct, and if maybeFileName is a Just, then we load this as file.
    -- This might fail as an ordinary load might. 
    
    stateAfterLoad <-
        case maybeFilename of
          Just filename ->
            cmdLoadModule filename 
              (initialState{ compOptions = addStandardLVMPath basepath (configOptions ++ (map show options)) })
          Nothing ->
            return initialState{ compOptions = addStandardLVMPath basepath configOptions }
    
    -- Enter read-eval-print loop
    loop stateAfterLoad

    return ()

addSlashIfNeeded :: String -> String
addSlashIfNeeded dir = 
    case reverse dir of
        '/' : _ -> dir
        '\\' : _ -> dir
        _ -> dir ++ [slash] -- "\\" for Windows, "/" for UNIX

loop :: State -> IO State
loop state = do
    putStr (prompt state)
    hFlush stdout
    command' <- getLine
    let command = trim command'
    newState <- case command of
        (':':cmd:rest) -> 
            processCommand (toLower cmd) (trim rest) state
        (':':_) -> do
            putStrLn "Expecting command after colon. Type :? for help"
            return state
        expression -> do
            if null expression 
              then return state
              else processExpression expression state
    loop newState
  where
    prompt :: State -> String
    prompt State{ maybeModName = Nothing} = "Prelude> "
    prompt State{ maybeModName = Just modName} = modName ++ "> "
  
processCommand :: Char -> String -> State -> IO State
processCommand cmd rest state = 
    case cmd of
        '!' -> cmdSystem       rest state
        't' -> cmdShowType     rest state
        'l' -> cmdLoadModule   rest state
        'r' -> cmdReloadModule      state
        'a' -> cmdAlert        rest state
        'b' -> cmdBrowse            state
        'h' -> cmdHelp              state
        '?' -> cmdHelp              state
        'q' -> do   putStrLn "[Leaving texthint]"
                    exitWith ExitSuccess
        _   -> do   putStrLn "Command not recognised.  Type :? for help"
                    return state

------------------------
-- Command :!
------------------------
        
cmdSystem :: String -> State -> IO State
cmdSystem command state = do       
    system command
    return state

------------------------
-- Command :t
------------------------

cmdShowType :: String -> State -> IO State
cmdShowType [] state = do
    putStrLn "ERROR: Expecting expression after :t"
    return state
cmdShowType expression state = do
    let moduleContents = expressionModule expression state
    writeInternalModule moduleContents state
    (success, output) <- compileInternalModule "-i" state
    if success then do
        let typeLine = filter (interpreterMain `isPrefixOf`) (map trim (lines output))
        unless (null typeLine) $ do
            let typeString = 
                      trim
                    . dropWhile (== ':')
                    . dropWhile isSpace
                    . drop (length interpreterMain) 
                    . head
                    $ typeLine
            putStrLn (expression ++ " :: " ++ typeString)
      else
        putStr (removeEvidence output)
    return state

------------------------
-- Command :l 
------------------------

cmdLoadModule :: String -> State -> IO State
cmdLoadModule [] state = -- unload
    return state{maybeModName = Nothing, maybeFileName = Nothing }
cmdLoadModule fileName state = do
    fileExists <- doesFileExist fileName
    if fileExists 
      then loadExistingModule fileName state
      else do
        let fileNameWithHS = fileName ++ ".hs"
        fileExistsWithHS <- doesFileExist fileNameWithHS
        if fileExistsWithHS
          then loadExistingModule fileNameWithHS state
          else do
            putStr $ "ERROR - Unable to open file \"" ++ fileName ++ "\"\n"
            return state

loadExistingModule :: String -> State -> IO State
loadExistingModule fileName state = do
    let (path, baseName, _) = splitFilePath fileName
    unless (null path) $
        setCurrentDirectory path
    let newState = state{ maybeModName = Just baseName, maybeFileName = Just fileName }
        moduleContents = expressionModule "()" newState
    writeInternalModule moduleContents newState
    (_, output) <- compileInternalModule "" newState
    putStr (removeEvidence output)
    return newState 

------------------------
-- Command :r
------------------------

cmdReloadModule :: State -> IO State
cmdReloadModule state = 
    case maybeModName state of
        Nothing -> return state
        Just name -> cmdLoadModule name state

------------------------
-- Command :a 
------------------------

cmdAlert :: String -> State -> IO State
cmdAlert msg state = do
    let (invocation, outputFilePath) = getPreviousInvocation
    -- putStrLn (" -- " ++ invocation ++ " -- " ++ outputFilePath)
    when (invocation /= "") 
      (do 
        (_, output) <- execCompileModule (invocation ++ " --alert=\"" ++ escape alertESCAPABLES msg ++ "\" -b --enable-logging ") outputFilePath
        putStr (removeEvidence output)
        return ())
    return state

------------------------
-- Command :b
------------------------

cmdBrowse :: State -> IO State
cmdBrowse state = 
    case maybeModName state of
        Nothing -> do
            let moduleContents = "import Prelude\n"
            writeInternalModule moduleContents state
            (_, output) <- compileInternalModule "-I -3 -B" state
            putStr (unlines (safeTail (lines output)))
            return state
        Just modName -> do
            (_, output) <- compileModule modName "-i -3 -B" state
            putStr (unlines (safeTail (lines output)))
            return state

------------------------
-- Command :?
------------------------

cmdHelp :: State -> IO State
cmdHelp state = do
    putStrLn ":h, :?           display this help screen"
    putStrLn ":l <filename>    load module"
    putStrLn ":l               unload module"
    putStrLn ":r               reload module"
    putStrLn ":a <message>     alert to previous compile (message optional)"
    putStrLn ":t <expression>  show type of expression"
    putStrLn ":b               browse definitions in current module"
    putStrLn ":! <command>     shell command"
    putStrLn ":q               quit"
    return state

------------------------
-- Expression 
------------------------

processExpression :: String -> State -> IO State
processExpression expression state = do
    removeLVM state
    let moduleContents = expressionModule expression state
    writeInternalModule moduleContents state
    (success, output) <- compileInternalModule "" state
    putStr (removeEvidence output)
    when success $ 
        executeInternalModule state
    return state

------------------------
-- Interpreter module 
------------------------

outputFileName, internalModule, interpreterMain :: String
outputFileName = "InterpreterOutput.txt"        
internalModule = "Interpreter"
interpreterMain = "interpreter_main"

internalModulePath :: State -> String
internalModulePath state = tempDir state ++ internalModule

writeInternalModule :: String -> State -> IO ()
writeInternalModule contents state =
    writeModule (internalModulePath state) contents

writeModule :: String -> String -> IO ()
writeModule modulePath contents = do
    let hsFile = modulePath ++ ".hs"
    writeFile hsFile contents
        `catch` (\_ -> fatal ("Unable to write to file \"" ++ hsFile ++ "\""))

compileInternalModule :: String -> State -> IO (Bool, String)
compileInternalModule options state =
    compileModule (internalModulePath state) options state

compileModule :: String -> String -> State -> IO (Bool, String)
compileModule fileName options state = do
    let outputFilePath = tempDir state ++ outputFileName
    -- putStrLn (fileName ++ "." ++ options ++ "." ++ unwords (compOptions state))
    -- mapM putStrLn (compOptions state)
    let heliumInvocation = "\"" ++ binDir state ++ "helium\" " ++ " " ++ unwords (compOptions state) 
                                ++ " " ++ options ++ " " ++ fileName
    setPreviousInvocation heliumInvocation outputFilePath
    execCompileModule heliumInvocation outputFilePath

verbose = isInfixOf "--verbose" 

execCompileModule :: String -> String -> IO (Bool, String)
execCompileModule invocation outputFilePath = do
    when (verbose invocation) $
      putStrLn invocation
    exitCode <- sys (invocation ++ " > " ++ outputFilePath)
    contents <- readFile outputFilePath
                `catch` (\_ -> fatal ("Unable to read from file \"" ++ outputFilePath ++ "\""))
    return (exitCode == ExitSuccess, contents)
    
executeInternalModule :: State -> IO ()
executeInternalModule state =
    executeModule (internalModulePath state) state

lvmOptionsFilter :: [String] -> String
lvmOptionsFilter opts = 
  case lvmPathFromOptions (simplifyOptions (argsToOptions opts)) of
    Nothing      -> ""
    (Just paths) -> "-P" ++ paths

executeModule :: String -> State -> IO ()
executeModule fileName state = do
    let invocation = "\"" ++ binDir state ++ "lvmrun\" " ++ lvmOptionsFilter (compOptions state) ++ " \""++ fileName ++ "\""
    -- putStrLn invocation
    sys invocation
    return ()

removeLVM :: State -> IO ()
removeLVM state = do
    let lvmFile = tempDir state ++ internalModule ++ ".lvm"
    lvmExist <- doesFileExist lvmFile
    when lvmExist $ removeFile lvmFile

expressionModule :: String -> State -> String
expressionModule expression state =
    unlines
    (  case maybeModName state of 
        Nothing -> []
        Just name -> [ "import " ++ name ]
    ++ [ interpreterMain ++ " = " ++ expression ]
    )

sys s = do
    -- putStrLn ("System:" ++ s)
    system s

------------------------
-- Remove evidence 
------------------------

-- remove evidence that there is an Interpreter module 
-- that is compiled each time you type an expression
-- or ask for a type

removeEvidence :: String -> String
removeEvidence = 
    unlines . firstState . lines
  where
    firstState :: [String] -> [String]
    firstState [] = []
    firstState (line:lines)
        | "Compiling" `isPrefixOf` line && 
                (internalModule ++ ".hs") `isSuffixOf` line =
            interpreterState [] lines
        | "Compiling" `isPrefixOf` line =
            line : otherModuleState lines
        | "is up to date" `isSuffixOf` line =
            firstState lines
        | otherwise =
            line : firstState lines
    
    interpreterState soFar [] = soFar
    interpreterState soFar (line:lines) 
        | "Compilation successful" `isPrefixOf` line =
            firstState lines
        | "Compilation" `isPrefixOf` line = 
            map removePositions soFar ++ firstState lines
        | otherwise =
            interpreterState (soFar ++ [line]) lines

    otherModuleState [] = []
    otherModuleState (line:lines)  
        | "Compilation" `isPrefixOf` line = 
            line : firstState lines
        | otherwise = 
            line : otherModuleState lines
    
    removePositions line = 
        let (upToColon, rest) = span (/= ':') line
        in if not (all isSpace upToColon) &&
                all (\c -> isDigit c || c `elem` "(), ") upToColon then
            safeTail rest
           else 
            line

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

-- As copied from Logger.hs

escapeChar = '\\';

alertESCAPABLES :: String
alertESCAPABLES     = ['"', escapeChar]

-- Escapes all characters from the list escapables
escape :: [Char] -> String -> String
escape _          []     = []
escape escapables (x:xs) = 
    if (x `elem` escapables) 
      then escapeChar : rest 
      else rest
    where 
      rest = x:(escape escapables xs)

