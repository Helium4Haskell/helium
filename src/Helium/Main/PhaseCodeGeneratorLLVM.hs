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
import Text.PrettyPrint.Leijen

phaseCodeGeneratorLLVM :: String -> CoreModule -> [Option] -> IO ()
phaseCodeGeneratorLLVM fullName coreModule options = do
    enterNewPhase "Code generation LLVM" options

    supply <- newNameSupply
    let supplyDesugar : supplyFromCore : _ = splitNameSupplies supply

    let simplified = desugarCore supplyDesugar coreModule
    putDoc $ pretty simplified

    let imperative = fromCore supplyFromCore simplified
    print imperative

    
