module Main where

import Prelude
import System
import IO 
import Monad
import Char
import List
import OSSpecific

data State = 
    State
    { modName :: Maybe String
    , tempDir :: String
    }

prompt :: State -> String
prompt State{ modName = Nothing} = "Prelude> "
prompt State{ modName = Just modName} = modName ++ "> "

main = do
    -- Find TEMP directory
    dir' <- getEnv "TEMP" `catch` (\_ -> do
                putStrLn "Can't find environment variable TEMP"
                putStrLn "Please set this variable to a temporary directory"
                exitWith (ExitFailure 1)
           )
    let dir = trim dir'
        dirPlusSlash = case reverse dir of
                            '/' : _ -> dir
                            '\\' : _ -> dir
                            _ -> dir ++ slash -- "\\" for Windows, "/" for UNIX
    
    -- State is temp dir and maybe a currently loaded module
    let initialState = State { tempDir = dirPlusSlash, modName = Nothing }
    
    -- Logo
    putStrLn header
    
    -- Load command-line parameter module
    args <- getArgs
    stateAfterLoad <-
        if length args == 1 then
            processSpecial ("l " ++ head args) initialState
        else
            return initialState
            
    -- Enter read-eval-print loop            
    loop stateAfterLoad
    
    return ()

loop :: State -> IO State
loop state = do
    putStr (prompt state)
    hFlush stdout
    command' <- getLine
    let command = trim command'
    newState <- case command of
        (':':cmd:rest) -> 
            processSpecial (toLower cmd : rest) state
        (':':_) -> do
            putStrLn "Expecting command after :. Type :? for a list of commands"
            return state
        expression -> do
            if null expression 
                then return ()
                else processExpression expression state
            return state
    loop newState

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

processSpecial :: String -> State -> IO State

processSpecial ('!':rest) state = do
    system (trim rest)
    return state

processSpecial ('t':rest) state = 
    let expression = trim rest
    in if not (null expression) then do
            writeModule expression state
            (success, output) <- compile "-t" state
            if success then do
                let typeLine = filter (interpreterMain `isPrefixOf`) (lines output)
                if null typeLine then
                    return ()
                  else 
                    let typeString = 
                              trim
                            . dropWhile (== ':')
                            . dropWhile isSpace
                            . drop (length interpreterMain) 
                            . head
                            $ typeLine
                    in putStrLn (expression ++ " :: " ++ typeString)
              else
                putStr output
            return state
       else do
            putStrLn "ERROR: Expecting expression after :t"
            return state
       
processSpecial ('l':rest) state =
    let moduleName = trim rest
    in if null moduleName then
            return (state { modName = Nothing })
       else if not (isModuleName moduleName) then do
            putStrLn "ERROR: Expecting module name after :l"
            return state
       else do
            let newState = state { modName = Just moduleName }
            writeModule "()" newState
            (success, output) <- compile "" state
            putStr output
            return (if success then newState else state)
            
processSpecial ('q':_) _ = 
    exitWith ExitSuccess
    
processSpecial ('?':_) state = do
    putStrLn ":l <module>      Load a module"
    putStrLn ":t <expression>  Show type of expression"
    putStrLn ":! <command>     Shell command"
    putStrLn ":q               Quit"
    return state
    
processSpecial _ state = do
    putStrLn "Unknown command, press :? for all commands" 
    return state
    
isModuleName :: String -> Bool
isModuleName str@(first:_) = all isAlphaNum str && isUpper first
isModuleName _ = False

processExpression :: String -> State -> IO ()
processExpression expression state = do
    writeModule expression state
    (success, output) <- compile "" state
    putStr (removeUpToDateLines output)
    when success $ do
        let cmd = "lvmrun " ++ tempDir state ++ internalModule ++ ".lvm"
        system cmd
        return ()

compile :: String -> State -> IO (Bool, String)
compile options state = do
    let outputFilePath = tempDir state ++ outputFileName
    exitCode <- system ("helium " ++ options ++ " " ++ tempDir state ++ internalModule ++ ".hs" ++
                            "> " ++ outputFilePath)
    contents <- readFile outputFilePath
                `catch` (\_ -> fatal ("Can't read from file " ++ show outputFilePath))
    let newContents = removeEvidence contents state
    case exitCode of 
        ExitSuccess -> return (True, newContents)
        _ -> return (False, newContents)
        
outputFileName = "InterpreterOutput.txt"        
internalModule = "Interpreter"
interpreterMain = "interpreter_main"

writeModule :: String -> State -> IO ()
writeModule expression state = do
    let hiFile = tempDir state ++ internalModule ++ ".hs"
    writeFile 
        hiFile
        (makeModule expression state)
            `catch` (\_ -> fatal ("Can't write to file " ++ show hiFile))

fatal msg = do    
    putStrLn msg
    putStrLn "Make sure that the environment variable TEMP points to a valid directory"
    exitWith (ExitFailure 1)

makeModule :: String -> State -> String
makeModule expression state =
    unlines
    (  {- [ "module " ++ internalModule ++ " where" ]
    ++  -}
       (case modName state of Nothing -> []; Just modName -> [ "import " ++ modName ])
    ++ [ interpreterMain ++ " = " ++ expression ]
    )

header :: String
header = unlines
    [ " _          _ _                 "
    , "| |        | (_)                   "
    , "| |__   ___| |_ _   _ _ __ ___     -- Welcome to the Helium interpreter --"
    , "| '_ \\ / _ \\ | | | | | '_ ` _ \\    ---------------------------------------"
    , "| | | |  __/ | | |_| | | | | | |   -- Type an expression to evaluate    --"
    , "|_| |_|\\___|_|_|\\__,_|_| |_| |_|   --    or a command (:? for a list)   --"
    ]

removeEvidence :: String -> State -> String
removeEvidence output state = 
    let 
        outputLines = lines output
        (linesBefore, rest') = 
            span (not . (("Compiling " ++ tempDir state) `isPrefixOf`)) outputLines
        rest = safeTail rest'
        (linesBetween, result') =  
            span (not . ("Compilation" `isPrefixOf`)) rest
        result = safeTail result'
    in
        unlines (linesBefore ++ 
                 filter 
                    (\line -> not (line `contains` interpreterMain) || interpreterMain `isPrefixOf` line) 
                    linesBetween ++ 
                 result)

removeUpToDateLines :: String -> String
removeUpToDateLines =
      unlines
    . filter (not . ("is up to date" `isSuffixOf`))
    . lines
    
safeTail :: [a] -> [a]
safeTail [] = []
safeTail (_:tl) = tl

contains :: Eq a => [a] -> [a] -> Bool
_  `contains` [] = True
[] `contains` _  = False
(large@(_:tail)) `contains` small = 
    small `isPrefixOf` large || tail `contains` small 
