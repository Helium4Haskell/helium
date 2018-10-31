{-| Module      :  PhaseCodeGeneratorLLVM
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorLLVM(phaseCodeGeneratorLLVM) where

import Lvm.Common.Id(newNameSupply, splitNameSupplies)
import Lvm.Core.Expr(CoreModule)
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Core(desugarCore)
import Helium.CodeGeneration.Iridium.FromCore(fromCore)
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.LLVM.CompileModule(compileModule)
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)
import Text.PrettyPrint.Leijen

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorLLVM :: String -> CoreModule -> [Option] -> IO ()
phaseCodeGeneratorLLVM fullName coreModule options = do
  enterNewPhase "Code generation LLVM" options

  supply <- newNameSupply
  let supplyDesugar : supplyFromCore : supplyToLLVM : _ = splitNameSupplies supply

  let simplified = desugarCore supplyDesugar coreModule

  let iridium = fromCore supplyFromCore simplified

  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName

  writeFile (fullNameNoExt ++ ".iridium") $ show iridium

  let target = Target 64 48
  let llvm = compileModule (envForModule target iridium) supplyToLLVM iridium

  writeFile (fullNameNoExt ++ ".ll") $ Text.unpack $ ppllvm llvm
