module Helium.Main.Make (make) where

import Helium.Main.Compile(compile)
import Helium.Parser.Parser(parseOnlyImports)
import qualified Helium.CodeGeneration.Iridium.FileCache as Iridium
import Control.Monad
import System.FilePath(joinPath)
import Data.List(nub, elemIndex, isSuffixOf, isPrefixOf, intercalate)
import Data.Maybe(fromJust, mapMaybe, catMaybes)
import Helium.Lvm.Path(explodePath,getLvmPath)
import System.Directory(doesFileExist, getModificationTime,
                        getPermissions, Permissions(writable))
import Helium.Main.Args
import Helium.Main.CompileUtils
import Helium.Utils.Utils
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Syntax
import Data.IORef
import qualified Helium.Lvm.Core.Module as Lvm
import Helium.Lvm.Common.Id (Id, stringFromId, idFromString)
import qualified Helium.Lvm.Core.Parsing.Parser as Lvm
import qualified Helium.Lvm.Core.Parsing.Lexer as Lvm
import qualified Helium.Lvm.Core.Parsing.Layout as Lvm
import qualified Helium.Lvm.Core.Module as Lvm
import qualified Helium.Lvm.Core.Expr as Lvm

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
make :: String -> String -> [String] -> [String] -> [Option] -> Iridium.FileCache -> IORef [(String, Bool)] -> IO Bool
make basedir fullName lvmPath chain options iridiumCache doneRef = do
  -- If we already compiled this module, return the result we already know
  done <- readIORef doneRef

  case lookup fullName done of 
    Just isRecompiled -> return isRecompiled
    Nothing -> do
      let (_, name, ext) = splitFilePath fullName
      imports <- case ext of
        "hs" -> ((if name == "Prelude" then [] else ["Prelude", "HeliumLang"]) ++) <$> do
          ims <- parseOnlyImports fullName
          return (map show ims)
        "core" -> parseCoreOnlyImports fullName
        "iridium" -> return []

      let chainNames = map nameFromString chain

      -- If this module imports a module earlier in the chain, there is a cycle
      case circularityCheck (map nameFromString imports) chainNames of
          Just cycl -> do
            showErrorsAndExit [CircularImport cycl] 1
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
            make basedir importFullName lvmPath (chain ++ [importModuleName]) options iridiumCache doneRef

      -- Recompile the current module if:
      --  * any of the children was recompiled
      --  * the build all option (-B) was on the command line
      --  * the build one option (-b) was there and we are 
      --      compiling the top-most module (head of chain)
      --  * the module is not up to date (.hs newer than .lvm or .iridium)
      let (filePath, moduleName, _) = splitFilePath fullName
      upToDate <- upToDateCheck (combinePathAndFile filePath moduleName) ext
      newDone <- readIORef doneRef
      isRecompiled <- 
          if or compileResults || 
              BuildAll `elem` options || 
              (BuildOne `elem` options && length chain > 0 && moduleName == head chain) ||
              not upToDate 
            then do
              compile basedir fullName options lvmPath iridiumCache (map fst newDone)
              return True
            else do
              putStrLn (moduleName ++ " is up to date")
              return False

      -- Remember the fact that we have already been at this module
      writeIORef doneRef ((fullName, isRecompiled):newDone)
      return isRecompiled

circularityCheck :: [Name] -> [Name] -> Maybe [Name]
circularityCheck (import_:imports) chain =
    case elemIndex import_ chain of
        Just index -> Just (drop index chain ++ [import_])
        Nothing -> circularityCheck imports chain
circularityCheck [] _ = Nothing

-- | upToDateCheck returns true if the .iridium is newer than the .hs
upToDateCheck :: String -> String -> IO Bool
upToDateCheck _ "iridium" = return False
upToDateCheck basePath ext = do
    let irPath = basePath ++ ".iridium"
        sourcePath = basePath ++ "." ++ ext
    irExists <- doesFileExist irPath
    if irExists then do
        t1 <- getModificationTime sourcePath
        t2 <- getModificationTime irPath
        if t1 == t2
          then do -- If the times are equal and the files are not writable,
                -- we assume that it was installed in a system directory
                -- and therefore consider it up to date.
               let isReadOnly file = (not . writable) `fmap` getPermissions file
               irReadOnly <- isReadOnly irPath
               hsReadOnly <- isReadOnly sourcePath
               -- Up to date if both are read only (and of equal mod time)
               return (irReadOnly && hsReadOnly)
          else return (t1 < t2)
     else
        return False

-- TODO: Use a faster parser that only finds the dependencies and does not parse the whole file
parseCoreOnlyImports :: FilePath -> IO [String]
parseCoreOnlyImports fullName =
  do
    coreModule <- readCore fullName
    return $ map stringFromId $ nub $ Lvm.moduleImports coreModule

readCore :: FilePath -> IO Lvm.CoreModule
readCore fullName = do
  contents <- readSourceFile fullName
  let tokens = Lvm.layout $ Lvm.lexer (1,1) contents
  Lvm.parseModule fullName tokens
