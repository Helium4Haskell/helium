{-| Module      :  PhaseCodeGeneratorIridium
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseCodeGeneratorIridium(phaseCodeGeneratorIridium) where

import Lvm.Common.Id(NameSupply, newNameSupply, splitNameSupplies, mapWithSupply)
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import Lvm.Common.Id(idFromString)
import Helium.Main.CompileUtils
import Helium.CodeGeneration.Core(desugarCore)
import Helium.CodeGeneration.Iridium.FromCore(fromCore)
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.Iridium.ResolveDependencies(resolveDependencies, IridiumFile(..))
import Helium.CodeGeneration.LLVM.CompileModule(compileModule)
import Helium.CodeGeneration.LLVM.Target(Target(..))
import Helium.CodeGeneration.LLVM.Env(envForModule)
import Text.PrettyPrint.Leijen

import qualified Data.Text.Lazy as Text
import LLVM.Pretty (ppllvm)

phaseCodeGeneratorIridium :: [String] -> String -> Core.CoreModule -> [Option] -> IO ([IridiumFile], Bool)
phaseCodeGeneratorIridium paths fullName coreModule options = do
  enterNewPhase "Code generation" options

  putStrLn $ show $ pretty coreModule

  supply <- newNameSupply
  let supplyDesugar : supplyFromCore : supplyToLLVM : _ = splitNameSupplies supply

  let simplified = desugarCore supplyDesugar coreModule

  -- Check whether the module has a 'main$' function
  let hasMain = any ((== idFromString "main$") . Core.declName) $ Core.moduleDecls coreModule

  let iridium = fromCore supplyFromCore simplified

  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName

  writeFile (fullNameNoExt ++ ".iridium") $ show iridium

  let file = IridiumFile (fullNameNoExt ++ ".iridium") iridium True
  files <-
    if hasMain then
      resolveDependencies paths [file]
    else
      return [file]

  let target = Target 64 48
  sequence_ $ mapWithSupply (compileToLlvm target) supplyToLLVM files

  return (files, hasMain)

compileToLlvm :: Target -> NameSupply -> IridiumFile -> IO ()
compileToLlvm _ supply (IridiumFile _ _ False) = return ()
compileToLlvm target supply (IridiumFile fullName iridium _) = do
  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName
  let llvm = compileModule (envForModule target iridium) supply iridium
  writeFile (fullNameNoExt ++ ".ll") $ Text.unpack $ ppllvm llvm
