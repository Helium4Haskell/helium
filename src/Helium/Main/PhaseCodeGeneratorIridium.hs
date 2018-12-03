{-| Module      :  PhaseCodeGeneratorIridium
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorIridium(phaseCodeGeneratorIridium) where

import Lvm.Common.Id(NameSupply, splitNameSupplies, mapWithSupply, idFromString)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Core(desugarCore)
import Helium.CodeGeneration.Iridium.FromCore(fromCore)
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.Iridium.PassThunkArity(passThunkArity)
import Helium.CodeGeneration.Iridium.ResolveDependencies(resolveDependencies, IridiumFile(..))
import Helium.CodeGeneration.LLVM.CompileModule(compileModule)
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorIridium :: NameSupply -> [String] -> String -> Core.CoreModule -> [Option] -> IO ([IridiumFile], Bool)
phaseCodeGeneratorIridium supply paths fullName coreModule options = do
  enterNewPhase "Code generation for Iridium" options

  let supplyDesugar : supplyFromCore : supplyPassThunkArity : _ = splitNameSupplies supply

  let simplified = desugarCore supplyDesugar coreModule

  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName

  -- Check whether the module has a 'main$' function
  let hasMain = any ((== idFromString "main$") . Core.declName) $ Core.moduleDecls coreModule

  let iridium' = fromCore supplyFromCore simplified
  let iridium = passThunkArity supplyPassThunkArity iridium'

  writeFile (fullNameNoExt ++ ".iridium") $ show iridium

  let file = IridiumFile (fullNameNoExt ++ ".iridium") iridium True
  files <-
    if hasMain then
      resolveDependencies paths [file]
    else
      return [file]

  return (files, hasMain)
