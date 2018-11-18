module Helium.Main.Make (make) where

import Helium.Main.Compile(compile)
import Helium.Parser.Parser(parseOnlyImports)
import Control.Monad
import System.FilePath(joinPath)
import Data.List(nub, elemIndex, isSuffixOf, isPrefixOf, intercalate)
import Data.Maybe(fromJust, mapMaybe)
import Lvm.Path(explodePath,getLvmPath,searchPath,searchPathMaybe)
import System.Directory(doesFileExist, getModificationTime,
                        getPermissions, Permissions(writable))
import Helium.Main.Args
import Helium.Main.CompileUtils
import Helium.Utils.Utils
import Data.IORef
import qualified Lvm.Core.Module as Lvm
import Lvm.Common.Id (Id, stringFromId)
import qualified Lvm.Core.Parsing.Parser as Lvm
import qualified Lvm.Core.Parsing.Lexer as Lvm
import qualified Lvm.Core.Parsing.Layout as Lvm
import qualified Lvm.Core.Module as Lvm
import qualified Lvm.Core.Expr as Lvm

-- Prelude will be treated specially
prelude :: String
prelude = "Prelude.hs"

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
            let (_, _, ext) = splitFilePath fullName
            imports <- case ext of
              "hs" -> (["HeliumLang", "Prelude"] ++) <$> parseOnlyImports fullName
              "core" -> parseCoreOnlyImports fullName
              "iridium" -> return []

            print imports
            
            -- If this module imports a module earlier in the chain, there is a cycle
            case circularityCheck imports chain of
                Just cycl -> do
                      putStrLn $ "Circular import chain: \n\t" ++ showImportChain cycl ++ "\n"
                      exitWith (ExitFailure 1)
                Nothing -> 
                    return ()
                        
            -- Find all imports in the search path
            resolvedImports <- mapM (resolve lvmPath) imports
            
            -- For each of the imports...
            compileResults <- forM (zip imports resolvedImports) 
              $ \(importModuleName, maybeImportFullName) -> do

                -- Issue error if import can not be found in the search path
                case maybeImportFullName of
                    Nothing -> do
                        putStrLn $ 
                            "Can't find module '" ++ importModuleName ++ "'\n" ++ 
                            "Import chain: \n\t" ++ showImportChain (chain ++ [importModuleName]) ++
                            "\nSearch path:\n" ++ showSearchPath lvmPath
                        exitWith (ExitFailure 1)
                    Just _ -> return ()

                let importFullName = fromJust maybeImportFullName
                -- TODO : print names imported modules in verbose mode.
                
                -- If we only have an Iridium file we do not need to (/can't) recompile 
                if ".iridium" `isSuffixOf` importFullName then
                    return False
                  else
                    make basedir importFullName lvmPath (chain ++ [importModuleName]) options doneRef

            -- Recompile the current module if:
            --  * any of the children was recompiled
            --  * the build all option (-B) was on the command line
            --  * the build one option (-b) was there and we are 
            --      compiling the top-most module (head of chain)
            --  * the module is not up to date (.hs newer than .lvm or .iridium)
            let (filePath, moduleName, _) = splitFilePath fullName
            upToDate <- upToDateCheck (combinePathAndFile filePath moduleName)
            newDone <- readIORef doneRef
            isRecompiled <- 
                if or compileResults || 
                    BuildAll `elem` options || 
                    (BuildOne `elem` options && moduleName == head chain) ||
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
            
showImportChain :: [String] -> String
showImportChain = intercalate " imports "

showSearchPath :: [String] -> String
showSearchPath = unlines . map ("\t" ++)

preludeImportsPrelude :: [String] -> Bool 
preludeImportsPrelude [x,y] = x == prelude && y == prelude
preludeImportsPrelude _ = False

circularityCheck :: [String] -> [String] -> Maybe [String]
circularityCheck (import_:imports) chain =
    case elemIndex import_ chain of
        Just index -> Just (drop index chain ++ [import_])
        Nothing -> circularityCheck imports chain
circularityCheck [] _ = Nothing

-- | upToDateCheck returns true if the .iridium is newer than the .hs
upToDateCheck :: String -> IO Bool
upToDateCheck basePath = do
    let lvmPath = basePath ++ ".lvm"
        irPath = basePath ++ ".iridium"
        hsPath = basePath ++ ".hs"
    lvmExists <- doesFileExist (lvmPath)
    irExists <- doesFileExist hsPath
    if lvmExists && irExists then do
        t1 <- getModificationTime hsPath
        t2 <- getModificationTime irPath
        t3 <- getModificationTime lvmPath
        if t1 == t2 && t1 == t3
          then do -- If the times are equal and the files are not writable,
                -- we assume that it was installed in a system directory
                -- and therefore consider it up to date.
               let isReadOnly file = (not . writable) `fmap` getPermissions file
               lvmReadOnly <- isReadOnly lvmPath
               hsReadOnly <- isReadOnly hsPath
               -- Up to date if both are read only (and of equal mod time)
               return (lvmReadOnly && hsReadOnly)
          else return (t1 < t2 && t1 < t3)
     else
        return False

-- TODO: Use a faster parser that only finds the dependencies and does not parse the whole file
parseCoreOnlyImports :: FilePath -> IO [String]
parseCoreOnlyImports fullName =
  do
    coreModule <- readCore fullName
    return $ nub $ mapMaybe importedModule $ Lvm.moduleDecls coreModule
  where
    importedModule :: Lvm.Decl a -> Maybe String
    importedModule decl = case Lvm.declAccess decl of
      Lvm.Imported{ Lvm.importModule = name } -> Just $ stringFromId name
      _ -> Nothing

resolveDeclarations :: [String] -> Id -> IO (Lvm.CoreModule)
resolveDeclarations paths name = do
  maybeFullNameLvm <- searchPathMaybe paths ".lvm" $ stringFromId name
  case maybeFullNameLvm of
    Just fullName -> do
      readCore fullName
    Nothing -> do
      fullName <- searchPath paths ".iridium" $ stringFromId name
      -- TODO: Extract declarations out of Iridium file
      return $ Lvm.Module name 0 0 []

readCore :: FilePath -> IO Lvm.CoreModule
readCore fullName = do
  contents <- readSourceFile fullName
  let tokens = Lvm.layout $ Lvm.lexer (1,1) contents
  Lvm.parseModule fullName tokens
