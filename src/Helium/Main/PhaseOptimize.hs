{-| Module      :  PhaseOptimize
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseOptimize(phaseOptimize) where

import Lvm.Core.Expr(CoreModule)
import Helium.Main.CompileUtils

import qualified Helium.Optimization.LVM_Syntax as LVM_Syntax
import Helium.Optimization.CountingAnalysis(countingAnalysis)
import qualified Helium.Optimization.Types as Types
import Text.PrettyPrint.Leijen (Pretty, pretty)

phaseOptimize :: CoreModule -> [Option] -> IO CoreModule
phaseOptimize coreModule options = do
    enterNewPhase "Code optimization" options

    let optimizeModule = LVM_Syntax.coreModule2OptimizeModule coreModule
    let showIt = LVM_Syntax.showIt optimizeModule
    putStrLn $ show $ showIt
    --let constraints = LVM_Syntax.constraints optimizeModule
    --putStrLn $ show $ constraints
    --putStrLn "Solved =>"
    --putStrLn $ show $ Types.solveConstraints constraints
    let optimizeModule' = countingAnalysis optimizeModule
    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.optimize") $ show . pretty $ optimizeModule'
    let coreModule' = LVM_Syntax.optimizeModule2CoreModule optimizeModule'
    return coreModule'
