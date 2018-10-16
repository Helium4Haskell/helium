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
-- import Helium.CodeGeneration.Iridium.PassRemoveAliasses(passRemoveAliasses)
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
  putDoc $ pretty simplified

  let imperative = fromCore supplyFromCore simplified
  print imperative
  -- let imperative' = passRemoveAliasses imperative
  -- print imperative'

  let target = Target 64
  let llvm = compileModule (envForModule target imperative) supplyToLLVM imperative
  putStrLn $ Text.unpack $ ppllvm llvm

  {-LLVM.withContext $ \context ->
    LLVM.withModuleFromAST context llvm $ \mod -> do
      byteString <- LLVM.moduleLLVMAssembly mod
      print byteString-}
