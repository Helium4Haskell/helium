{-| Module      :  CompileUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.CompileUtils
    ( module Helium.Main.CompileUtils
    , Option(..)
    , splitFilePath, combinePathAndFile
    , when, unless
    , exitWith, ExitCode(..), exitSuccess, getArgs
    , module Helium.ModuleSystem.ImportEnvironment
    , Module(..)
    ) where

import Helium.Main.Args(Option(..))
import Helium.StaticAnalysis.Messages.Messages(HasMessage)
import Helium.StaticAnalysis.Messages.HeliumMessages(sortAndShowMessages,sortMessages)
import Control.Monad
import Helium.Utils.Utils(splitFilePath, combinePathAndFile)
import System.Exit
import System.Environment(getArgs)
import Helium.Utils.Logger
import Helium.ModuleSystem.ImportEnvironment
import Helium.Syntax.UHA_Syntax(Module(..))
import Data.Maybe
import Lvm.Path(searchPathMaybe)
import System.FilePath (joinPath)
import System.Process(system)

type Phase err a = IO (Either [err] a)
type CompileOptions = ([Option], String, [String]) 

(===>) :: Phase err1 a -> (a -> Phase err2 b) -> Phase (Either err1 err2) b
p ===> f = 
   p >>= either (return . Left . map Left) 
                (f >=> return . either (Left . map Right) Right)

doPhaseWithExit :: HasMessage err => Int -> ([err] -> String) -> CompileOptions -> Phase err a -> IO a
doPhaseWithExit nrOfMsgs code (options, fullName, doneModules) phase =
   do result <- phase
      case result of
         Left errs ->
            do sendLog (code errs) fullName doneModules options
               showErrorsAndExit errs nrOfMsgs
         Right a ->
            return a

sendLog :: String -> String -> [String] -> [Option] -> IO ()
sendLog code fullName modules =
    logger code (Just (modules,fullName))
    
enterNewPhase :: String -> [Option] -> IO ()
enterNewPhase phase options =
   when (Verbose `elem` options) $
      putStrLn (phase ++ "...")

showErrorsAndExit :: HasMessage a => [a] -> Int -> IO b
showErrorsAndExit errors maximumNumber = do
    let someErrors = take maximumNumber (sortMessages errors)
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

makeCoreLib :: String -> String -> IO ()
makeCoreLib basepath name =
    do
      let bps = [basepath]
      maybeFullName <- searchPathMaybe bps ".lvm" name
      case maybeFullName of 
        Just _ -> return ()
        Nothing -> do
                     maybeCoreName <- searchPathMaybe bps ".core" name
                     case maybeCoreName of
                       Just _  -> sys ("coreasm " ++ joinPath [basepath, name])
                       Nothing -> do 
                                    putStr
                                      (  "Cannot find "
                                      ++ name ++ ".core in \n"
                                      ++ basepath)                                      
                                    exitWith (ExitFailure 1)

sys :: String -> IO ()
sys s = do
    -- putStrLn ("System:" ++ s)
    _ <- system s
    return ()
      
checkExistence :: [String] -> String -> IO ()
checkExistence path name =
    do
        maybeLocation <- resolve path name
        when (isNothing maybeLocation) $ do
            putStr
                (  "Cannot find "
                ++ name
                ++ ".hs (or .lvm) in search path:\n"
                ++ unlines (map ("\t" ++) path)
                ++ "Use the -P option to add paths to the search path.\n"
                )
            exitWith (ExitFailure 1)

resolve :: [String] -> String -> IO (Maybe String)
resolve path name = 
    do maybeFullName <- searchPathMaybe path ".hs" name
       case maybeFullName of
           Just fullName -> return (Just fullName)
           Nothing       -> searchPathMaybe path ".lvm" name
           
