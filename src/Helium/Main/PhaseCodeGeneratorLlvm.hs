-- | Module      :  PhaseCodeGeneratorLlvm
--    License     :  GPL
--
--    Maintainer  :  helium@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable
module Helium.Main.PhaseCodeGeneratorLlvm
  ( phaseCodeGeneratorLlvm,
  )
where

import Control.Monad (when)
import qualified Data.Text.Lazy as Text
import Helium.CodeGeneration.Iridium.ResolveDependencies (IridiumFile (..))
import Helium.CodeGeneration.LLVM.CompileModule (compileModule)
import Helium.CodeGeneration.LLVM.Env (envForModule)
import Helium.CodeGeneration.LLVM.Target (Target (..))
import Helium.Main.Args
import Helium.Main.CompileUtils
import LLVM.Pretty (ppllvm)
import Lvm.Common.Id (NameSupply, mapWithSupply, splitNameSupplies)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import System.Process

phaseCodeGeneratorLlvm :: NameSupply -> FilePath -> [IridiumFile] -> Bool -> [Option] -> IO ()
phaseCodeGeneratorLlvm supply output files shouldLink options = do
  enterNewPhase "Code generation for LLVM" options
  let target = Target 64 48
  sequence_ $ mapWithSupply (compileToLlvm target) supply files
  when shouldLink $ do
    let debug = if (containsDOption Memory `any` options) then "-DDEBUG" else ""
    let args = "-o" : output : "-O0" : debug : "../lib/runtime/runtime.c" : map toLlvmPath files
    (code, res, err) <- readProcessWithExitCode "clang" args ""
    case code of
      ExitSuccess -> return ()
      ExitFailure _ -> do
        putStrLn "Clang failed with the following errors:"
        putStrLn res
        putStrLn err
        putStrLn "Failed to link files. This is probably a bug of Helium. See errors above."
        exitWith (ExitFailure 1)
    return ()

compileToLlvm :: Target -> NameSupply -> IridiumFile -> IO ()
compileToLlvm _ supply (IridiumFile _ _ False) = return ()
compileToLlvm target supply ir@(IridiumFile f iridium _) = do
  let llvm = compileModule (envForModule target iridium) supply iridium
  writeFile (toLlvmPath ir) $ Text.unpack $ ppllvm llvm

toLlvmPath :: IridiumFile -> FilePath
toLlvmPath (IridiumFile fullName _ _) = fullNameNoExt ++ ".ll"
  where
    (path, baseName, _) = splitFilePath fullName
    fullNameNoExt = path ++ baseName
