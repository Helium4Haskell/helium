{-| Module      :  PhaseCodeGeneratorLlvm
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorLlvm(phaseCodeGeneratorLlvm) where

import Lvm.Common.Id(NameSupply, splitNameSupplies, mapWithSupply)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Iridium.ResolveDependencies(IridiumFile(..))
import Helium.CodeGeneration.LLVM.CompileModule(compileModule)
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)
import System.Process

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorLlvm :: NameSupply -> [IridiumFile] -> Bool -> [Option] -> IO ()
phaseCodeGeneratorLlvm supply files shouldLink options = do
  enterNewPhase "Code generation for LLVM" options

  let target = Target 64 48
  sequence_ $ mapWithSupply (compileToLlvm target) supply files

  if shouldLink then do
    let args = "-O3" : map toLlvmPath files
    print args
    (x, res, err) <- readProcessWithExitCode "clang" args ""
    putStrLn res
    unless (null err) $ do
      putStrLn "Clang error"
      putStrLn err
    return ()
  else return ()

  return ()

compileToLlvm :: Target -> NameSupply -> IridiumFile -> IO ()
compileToLlvm _ supply (IridiumFile _ _ False) = return ()
compileToLlvm target supply ir@(IridiumFile f iridium _) = do
  putStrLn f
  putStrLn $ toLlvmPath ir
  let llvm = compileModule (envForModule target iridium) supply iridium
  writeFile (toLlvmPath ir) $ Text.unpack $ ppllvm llvm

toLlvmPath :: IridiumFile -> FilePath
toLlvmPath (IridiumFile fullName _ _) = fullNameNoExt ++ ".ll"
  where
    (path, baseName, _) = splitFilePath fullName
    fullNameNoExt = path ++ baseName
