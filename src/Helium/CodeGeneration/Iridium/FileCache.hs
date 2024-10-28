{-| Module      :  FileCache
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- A cache which contains parsed Iridium files.

module Helium.CodeGeneration.Iridium.FileCache(FileCache, newFileCache, readIridium, readIridiumFile, writeIridium, parseIridium) where

import Helium.Lvm.Common.Id (Id, stringFromId)
import Helium.Lvm.Common.IdMap
import Data.IORef
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Show
import Helium.CodeGeneration.Iridium.Parse.Module (parseModuleIO)
import Helium.Utils.Utils (readSourceFile)
import Helium.Lvm.Path (searchPath)

data CachedFile = CachedFile !FilePath !Module

data FileCache = FileCache ![FilePath] !(IORef (IdMap CachedFile))

newFileCache :: [FilePath] -> IO FileCache
newFileCache paths = do
  ref <- newIORef emptyMap
  return $ FileCache paths ref

readIridium :: FileCache -> Id -> IO Module
readIridium cache name = snd <$> readIridiumFile cache name

readIridiumFile :: FileCache -> Id -> IO (FilePath, Module)
readIridiumFile cache@(FileCache paths ref) name = do
  files <- readIORef ref
  case lookupMap name files of
    Just (CachedFile path file) -> return (path, file)
    Nothing -> do
      fileName <- searchPath paths ".iridium" $ stringFromId name
      contents <- readSourceFile fileName
      file <- parseIridium cache name fileName contents
      return (fileName, file)

writeIridium :: FileCache -> FilePath -> Module -> IO ()
writeIridium (FileCache _ ref) fileName iridium = do
  writeFile fileName $ show iridium
  modifyIORef' ref $ insertMap (moduleName iridium) $ CachedFile fileName iridium

parseIridium :: FileCache -> Id -> FilePath -> String -> IO Module
parseIridium (FileCache _ ref) name fileName contents = do
  iridium <- parseModuleIO fileName contents
  modifyIORef' ref $ insertMap name (CachedFile fileName iridium)
  return iridium
