{-| Module      :  PhaseCodeGeneratorIridium
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorIridium(phaseCodeGeneratorIridium) where

import Helium.Lvm.Common.Id(NameSupply, splitNameSupplies, mapWithSupply, idFromString)
import qualified Helium.Lvm.Core.Expr as Core
import qualified Helium.Lvm.Core.Module as Core
import qualified Helium.CodeGeneration.Core.TypeCheck as Core
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Core(desugarCore)
import Helium.CodeGeneration.Iridium.FromCore(fromCore)
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.Iridium.FileCache
import Helium.CodeGeneration.Iridium.PassDeadCode(passDeadCode)
import Helium.CodeGeneration.Iridium.PassTailRecursion(passTailRecursion)
import Helium.CodeGeneration.Iridium.ResolveDependencies(resolveDependencies, IridiumFile(..))
import Helium.CodeGeneration.Iridium.TypeCheck
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)

import Text.PrettyPrint.Leijen (pretty)

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorIridium :: NameSupply -> FileCache -> String -> Core.CoreModule -> [Option] -> IO ([IridiumFile], Bool)
phaseCodeGeneratorIridium supply cache fullName coreModule options = do
  enterNewPhase "Code generation for Iridium" options

  let supplyDesugar : supplyFromCore : supplyPassDeadCode : supplyPassTailRecursion : _ = splitNameSupplies supply

  simplified <- desugarCore supplyDesugar coreModule

  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName

  writeFile (fullNameNoExt ++ ".test.core") $ show $ pretty simplified

  -- Check whether the module has a 'main' function
  let hasMain = any ((== idFromString "main") . Core.declName) $ Core.moduleDecls coreModule

  iridium' <- fromCore cache supplyFromCore simplified
  checkModuleIO "fromCore" (fullNameNoExt ++ ".iridium") iridium'

  let iridium = passTailRecursion supplyPassTailRecursion $ passDeadCode supplyPassDeadCode iridium'

  writeIridium cache (fullNameNoExt ++ ".iridium") iridium
  checkModuleIO "passTailRecursion" (fullNameNoExt ++ ".iridium") iridium

  let file = IridiumFile (fullNameNoExt ++ ".iridium") iridium True
  files <-
    if hasMain then
      resolveDependencies cache [file]
    else
      return [file]

  return (files, hasMain)
