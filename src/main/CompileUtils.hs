{-| Module      :  CompileUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module CompileUtils
    ( module CompileUtils
    , Option(..)
    , splitFilePath, combinePathAndFile
    , when, unless
    , exitWith, ExitCode(..)
    , sendLog
    , module ImportEnvironment
    , Module(..)
    ) where

import Args(Option(..))
import Messages(HasMessage)
import HeliumMessages(sortAndShowMessages)
import Monad(when, unless)
import Utils(splitFilePath, combinePathAndFile)
import System(exitWith, ExitCode(..))
import Logger
import ImportEnvironment
import UHA_Syntax(Module(..))

sendLog :: String -> String -> [String] -> [Option] -> IO ()
sendLog code fullName modules options =
    logger code (Just (modules,fullName)) (DebugLogger `elem` options)
    
enterNewPhase :: String -> [Option] -> IO ()
enterNewPhase phase options =
   when (Verbose `elem` options) $
      putStrLn (phase ++ "...")

showErrorsAndExit :: HasMessage a => [a] -> Int -> [Option] -> IO b
showErrorsAndExit errors maximumNumber options = do
    let someErrors = take maximumNumber errors
    showMessages someErrors
    when (number > maximumNumber) $ 
        putStrLn "(...)\n"
    putStrLn ("Compilation failed with " ++ show number ++
                " error" ++ (if number == 1 then "" else "s"))
    exitWith (ExitFailure 1)
  where
    number = length errors

showMessages :: HasMessage a => [a] -> IO ()
showMessages =
    putStr . sortAndShowMessages 
