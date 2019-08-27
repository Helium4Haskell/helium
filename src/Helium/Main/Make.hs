module Helium.Main.Make where

import Helium.Main.Compile(compile)
import Helium.Parser.Parser(parseOnlyImports)
import Control.Monad
import Data.List(elemIndex, isSuffixOf)
import Data.Maybe(fromJust)
import Lvm.Path()
import System.Directory(doesFileExist, getModificationTime,
                        getPermissions, Permissions(writable))
import Helium.Main.Args
import Helium.Main.CompileUtils
import Helium.Syntax.UHA_Syntax(Name)
import Helium.Syntax.UHA_Utils(nameFromString, getNameName)
import Helium.StaticAnalysis.Messages.StaticErrors
import Data.IORef

-- fullName = file name including path of ".hs" file that is to be compiled
-- lvmPath = where to look for files
-- chain = chain of imports that led to the current module
-- options = the compiler options
-- doneRef = an IO ref to a list of already compiled files
--                        (their names and whether they were recompiled or not)
-- returns: recompiled or not? (true = recompiled)
make :: String -> String -> [String] -> [String] -> [Option] -> IORef [(String, Bool)] -> IO Bool
make basedir fullName lvmPath chain options doneRef =
    do
        -- If we already compiled this module, return the result we already know
        done <- readIORef doneRef

        case lookup fullName done of
          Just isRecompiled -> return isRecompiled
          Nothing -> do

            imports <- parseOnlyImports fullName

            let chainNames = map nameFromString chain

            -- If this module imports a module earlier in the chain, there is a cycle
            case circularityCheck imports chainNames of
                Just cycl -> do
                      showErrorsAndExit [CircularImport cycl] 1
                Nothing ->
                    return ()

            -- Find all imports in the search path
            resolvedImports <- mapM (resolve lvmPath . getNameName) imports

            -- For each of the imports...
            compileResults <- forM (zip imports resolvedImports)
              $ \(importModuleName, maybeImportFullName) -> do

                -- Issue error if import can not be found in the search path
                case maybeImportFullName of
                    Nothing -> do
                        showErrorsAndExit [UnknownModule importModuleName chainNames lvmPath] 1
                        
                    Just _ -> return ()

                let importFullName = fromJust maybeImportFullName
                -- TODO : print names imported modules in verbose mode.

                -- If we only have an ".lvm" file we do not need to (/can't) recompile
                if ".lvm" `isSuffixOf` importFullName then
                    return False
                  else
                    make basedir importFullName lvmPath (chain ++ [getNameName importModuleName]) options doneRef

            -- Recompile the current module if:
            --  * any of the children was recompiled
            --  * the build all option (-B) was on the command line
            --  * the build one option (-b) was there and we are
            --      compiling the top-most module (head of chain)
            --  * the module is not up to date (.hs newer than .lvm)
            let (filePath, moduleName, _) = splitFilePath fullName
            upToDate <- upToDateCheck (combinePathAndFile filePath moduleName)
            newDone <- readIORef doneRef
            isRecompiled <-
                if or compileResults ||
                    BuildAll `elem` options ||
                    (BuildOne `elem` options && length chain > 0 && moduleName == head chain) ||
                    not upToDate
                    then do
                        compile basedir fullName options lvmPath (map fst newDone)
                        return True
                      else do
                        putStrLn (moduleName ++ " is up to date")
                        return False

            -- Remember the fact that we have already been at this module
            writeIORef doneRef ((fullName, isRecompiled):newDone)
            return isRecompiled


-- | upToDateCheck returns true if the .lvm is newer than the .hs
upToDateCheck :: String -> IO Bool
upToDateCheck basePath = do
    let lvmPath = basePath ++ ".lvm"
        hsPath = basePath ++ ".hs"
    lvmExists <- doesFileExist (lvmPath)
    if lvmExists then do
        t1 <- getModificationTime hsPath
        t2 <- getModificationTime lvmPath
        if t1 == t2
          then do -- If the times are equal and the files are not writable,
                -- we assume that it was installed in a system directory
                -- and therefore consider it up to date.
               let isReadOnly file = (not . writable) `fmap` getPermissions file
               lvmReadOnly <- isReadOnly lvmPath
               hsReadOnly <- isReadOnly hsPath
               -- Up to date if both are read only (and of equal mod time)
               return (lvmReadOnly && hsReadOnly)
          else return (t1 < t2)
     else
        return False

circularityCheck :: [Name] -> [Name] -> Maybe [Name]
circularityCheck (import_:imports) chain =
    case elemIndex import_ chain of
        Just index -> Just (drop index chain ++ [import_])
        Nothing -> circularityCheck imports chain
circularityCheck [] _ = Nothing
