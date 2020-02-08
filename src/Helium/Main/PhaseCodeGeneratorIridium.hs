-- | Module      :  PhaseCodeGeneratorIridium
--    License     :  GPL
--
--    Maintainer  :  helium@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable
module Helium.Main.PhaseCodeGeneratorIridium
  ( phaseCodeGeneratorIridium,
  )
where

import qualified Data.Text.Lazy as Text
import Helium.CodeGeneration.Core (desugarCore)
import qualified Helium.CodeGeneration.Core.TypeCheck as Core
import Helium.CodeGeneration.Iridium.FileCache
import Helium.CodeGeneration.Iridium.FromCore (fromCore)
import Helium.CodeGeneration.Iridium.PassDeadCode (passDeadCode)
import Helium.CodeGeneration.Iridium.PassTailRecursion (passTailRecursion)
import Helium.CodeGeneration.Iridium.ResolveDependencies (IridiumFile (..), resolveDependencies)
import Helium.CodeGeneration.Iridium.Show ()
import Helium.CodeGeneration.Iridium.TypeCheck
import Helium.CodeGeneration.LLVM.CompileModule (compileModule)
import Helium.CodeGeneration.LLVM.Env (envForModule)
import Helium.CodeGeneration.LLVM.Target (Target (..))
import Helium.Main.CompileUtils
import LLVM.Pretty (ppllvm)
import Lvm.Common.Id (NameSupply, idFromString, mapWithSupply, splitNameSupplies)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import Text.PrettyPrint.Leijen (pretty)

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
    if hasMain
      then resolveDependencies cache [file]
      else return [file]
  return (files, hasMain)
