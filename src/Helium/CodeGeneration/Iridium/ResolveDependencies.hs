{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Resolves the depencies of an Iridium module.

module Helium.CodeGeneration.Iridium.ResolveDependencies (resolveDependencies, IridiumFile(..)) where

import System.Exit
import Helium.Lvm.Path
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdSet
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.FileCache
import Helium.CodeGeneration.Iridium.Parse.Module(parseModuleIO)
import System.Directory(doesFileExist, getModificationTime)

data IridiumFile = IridiumFile
  { iridiumPath :: FilePath
  , iridiumModule :: Module
  -- * Should the LLVM be recompiled for this Iridium file?
  , iridiumShouldRecompile :: Bool
  }

-- Takes a list of modules, as some modules might already be parsed, as they were needed in the import phase
resolveDependencies :: FileCache -> [IridiumFile] -> IO [IridiumFile]
resolveDependencies cache modules = resolve cache worklist found modules
  where
    initialDependencies = modules >>= moduleDependencies . iridiumModule
    found' = setFromList $ fmap (moduleName . iridiumModule) modules
    found = foldr insertSet found' initialDependencies
    worklist = filter (not . (`elemSet` found')) initialDependencies

resolve :: FileCache -> [Id] -> IdSet -> [IridiumFile] -> IO [IridiumFile]
-- Worklist is empty, so all modules are resolved
resolve _ [] _ m = return m
resolve cache (x:xs) found m = do
  (path, iridium) <- readIridiumFile cache x

  let (filePath, moduleName, _) = splitFilePath path
  isUpToDate <- upToDate $ filePath ++ moduleName
  let m' = IridiumFile path iridium (not isUpToDate) : m
  let dependencies = filter (not . (`elemSet` found)) $ moduleDependencies iridium

  let found' = foldr insertSet found dependencies
  let xs' = dependencies ++ xs

  resolve cache xs' found' m'

-- Checks if the .ll is newer than the .iridium file
-- TODO: We also need to check whether the .ll file was compiled for the same target as we're currently using.
upToDate :: String -> IO Bool
upToDate basePath = do
  let llPath = basePath ++ ".ll"
  let irPath = basePath ++ ".iridium"
  llExists <- doesFileExist llPath
  if llExists then do
    t1 <- getModificationTime irPath
    t2 <- getModificationTime llPath
    return $ t1 < t2
  else
    return False
