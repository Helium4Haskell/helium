{-| Module      :  Data
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Resolves the depencies of an Iridium module.

module Helium.CodeGeneration.Iridium.ResolveDependencies (resolveDependencies, IridiumFile(..)) where

import System.Exit
import Lvm.Path
import Lvm.Common.Id
import Lvm.Common.IdSet
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Module(parseModule)

data IridiumFile = IridiumFile
  { iridiumPath :: FilePath
  , iridiumModule :: Module
  -- * Should the LLVM be recompiled for this Iridium file?
  , iridiumShouldRecompile :: Bool
  }

-- Takes a list of modules, as some modules might already be parsed, as they were needed in the import phase
resolveDependencies :: [String] -> [IridiumFile] -> IO [IridiumFile]
resolveDependencies paths modules = resolve paths worklist found modules
  where
    initialDependencies = modules >>= moduleDependencies . iridiumModule
    found = setFromList $ fmap (moduleName . iridiumModule) modules
    worklist = filter (not . (`elemSet` found)) initialDependencies

resolve :: [String] -> [Id] -> IdSet -> [IridiumFile] -> IO [IridiumFile]
-- Worklist is empty, so all modules are resolved
resolve paths [] found m = return m
resolve paths (x:xs) found m = do
  path <- searchPath paths ".iridium" $ stringFromId x
  file <- readFile path

  iridium <- case parseModule file of
    Left err -> do
      putStrLn $ "Failed to parse Iridium file " ++ show path
      print err
      exitWith (ExitFailure 1)
    Right ir -> return ir

  -- TODO: Check whether file should be recompiled
  let m' = IridiumFile path iridium False : m
  let dependencies = filter (not . (`elemSet` found)) $ moduleDependencies iridium

  let found' = foldr insertSet found dependencies
  let xs' = dependencies ++ xs

  resolve paths xs' found' m'
