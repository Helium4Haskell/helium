module Main where

import Parser(parseOnlyImports)
import Compile(compile)

import Monad(when, unless)
import List(nub, elemIndex, isSuffixOf, intersperse)
import System(exitWith, ExitCode(..), getArgs)
import Maybe(fromJust, isNothing)
import Standard(searchPathMaybe,getLvmPath)
import Directory(doesFileExist, getModificationTime)
import IOExts(writeIORef, newIORef, readIORef, IORef)
import Args
import Utils(splitFilePath)

main :: IO ()
main = do
    args                <- getArgs
    (options, fullName) <- processArgs args
    lvmPath             <- getLvmPath
    let (filePath, moduleName, extension) = splitFilePath fullName
        searchPath = filter (not.null).nub $ ".":filePath:lvmPath

    -- File must exist, this test doesn't use the search path
    fileExists <- doesFileExist fullName
    newFullName <- 
        if fileExists then 
            return fullName
        else do
            let filePlusHS = fullName ++ ".hs"
            filePlusHSExists <- doesFileExist filePlusHS
            when (not filePlusHSExists) $ do
                putStrLn $ "Can't find file " ++ show fullName ++ " or " ++ show filePlusHS
                System.exitWith (ExitFailure 1)
            return filePlusHS

    -- Libraries must exist somewhere in the search path
    mapM (checkExistence searchPath) 
        ["Prelude", "PreludePrim", "HeliumLang", "LvmLang", "LvmIO", "LvmException"]

    doneRef <- newIORef []
    make newFullName searchPath [moduleName] options doneRef
    return ()
    
-- fullName = file name including path of ".hs" file that is to be compiled
-- searchPath = where to look for files
-- chain = chain of imports that led to the current module
-- options = the compiler options
-- doneRef = an IO ref to a list of already compiled files
--                        (their names and whether they were recompiled or not)

-- returns: recompiled or not? (true = recompiled)

make :: String -> [String] -> [String] -> [Option] -> IORef [(String, Bool)] -> IO Bool
make fullName searchPath chain options doneRef =
    do
        -- If we already compiled this module, return the result we already now
        done <- readIORef doneRef
        case lookup fullName done of 
          Just isRecompiled -> return isRecompiled
          Nothing -> do
            imports <- parseOnlyImports fullName
            
            -- If this module imports a module earlier in the chain, there is a cycle
            case circularityCheck imports chain of
                Just cycle -> do
                    putStrLn $ "Circular import chain: \n\t" ++ showImportChain cycle ++ "\n"
                    System.exitWith (ExitFailure 1)
                Nothing -> 
                    return ()

            -- Find all imports in the search path
            resolvedImports <- mapM (resolve searchPath) imports

            -- For each of the imports...
            compileResults <- foreach (zip imports resolvedImports) 
              $ \(importModuleName, maybeImportFullName) -> do

                -- Issue error if import can not be found in the search path
                case maybeImportFullName of
                    Nothing -> do
                        putStrLn $ 
                            "Can't find module '" ++ importModuleName ++ "'\n" ++ 
                            "Import chain: \n\t" ++ showImportChain (chain ++ [importModuleName]) ++
                            "\nSearch path:\n" ++ showSearchPath searchPath
                        System.exitWith (ExitFailure 1)
                    Just _ -> return ()

                let importFullName = fromJust maybeImportFullName

                -- If we only have an ".lvm" file we do not need to (/can't) recompile 
                if ".lvm" `isSuffixOf` importFullName then
                    return False
                  else
                    make importFullName searchPath (chain ++ [importModuleName]) options doneRef

            -- Recompile the current module if:
            -- * any of the children was recompiled
            -- * the build option (-b) was on the command line
            -- * the module is not up to date (.hs newer than .lvm)
            let (filePath, moduleName, _) = splitFilePath fullName
            upToDate <- upToDateCheck (filePath ++ "/" ++ moduleName)
            newDone <- readIORef doneRef
            isRecompiled <- 
                if  any (==True) compileResults || Build `elem` options || not upToDate then do
                    compile fullName options (map fst newDone)
                    return True
                  else do
                    putStrLn (moduleName ++ " is up to date")
                    return False
            
            -- Remember the fact that we have already been at this module
            writeIORef doneRef ((fullName, isRecompiled):newDone)
            return isRecompiled
            
showImportChain :: [String] -> String
showImportChain = concat . intersperse " imports "

showSearchPath :: [String] -> String
showSearchPath = unlines . map ("\t" ++)

circularityCheck :: [String] -> [String] -> Maybe [String]
circularityCheck (import_:imports) chain =
    case elemIndex import_ chain of
        Just index -> Just (drop index chain ++ [import_])
        Nothing -> circularityCheck imports chain
circularityCheck [] chain = Nothing

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
                ++ "See the installation manual on setting the environment variable LVMPATH\n"
                )
            exitWith (ExitFailure 1)

foreach = flip mapM

resolve :: [String] -> String -> IO (Maybe String)
resolve path name = 
    do maybeFullName <- searchPathMaybe path ".hs" name
       case maybeFullName of
           Just fullName -> return (Just fullName)
           Nothing       -> searchPathMaybe path ".lvm" name

-- | upToDateCheck returns true if the .lvm is newer than the .hs
upToDateCheck :: String -> IO Bool
upToDateCheck basePath = do
    lvmExists <- doesFileExist (basePath ++ ".lvm")
    if lvmExists then do
        t1 <- getModificationTime (basePath ++ ".hs")
        t2 <- getModificationTime (basePath ++ ".lvm")
        return (t1 < t2)
     else
        return False
