{-| Module      :  PhaseCodeGeneratorLlvm
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorLlvm(phaseCodeGeneratorLlvm) where

import Lvm.Common.Id(NameSupply, newNameSupply, splitNameSupplies, mapWithSupply)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Iridium.ResolveDependencies(IridiumFile(..))
import Helium.CodeGeneration.LLVM.CompileModule(compileModule)
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorLlvm :: [IridiumFile] -> Bool -> [Option] -> IO ()
phaseCodeGeneratorLlvm files shouldLink options = do
  enterNewPhase "Code generation for LLVM" options

  let target = Target 64 48
  supply <- newNameSupply
  sequence_ $ mapWithSupply (compileToLlvm target) supply files

  return ()

compileToLlvm :: Target -> NameSupply -> IridiumFile -> IO ()
compileToLlvm _ supply (IridiumFile _ _ False) = return ()
compileToLlvm target supply (IridiumFile fullName iridium _) = do
  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName
  let llvm = compileModule (envForModule target iridium) supply iridium
  writeFile (fullNameNoExt ++ ".ll") $ Text.unpack $ ppllvm llvm
