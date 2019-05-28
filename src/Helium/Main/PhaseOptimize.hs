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
import Helium.Optimization.Pretty()
--import Helium.Optimization.CountingAnalysis(countingAnalysis)
import Helium.Optimization.StrictnessInfo(getLetBangs, showLetBangs)
--import qualified Helium.Optimization.Types as Types
import Text.PrettyPrint.Leijen(pretty)

phaseOptimize :: String -> CoreModule -> [Option] -> Bool -> IO CoreModule
phaseOptimize fullName coreModule options isTopMostModule = do
    enterNewPhase "Code optimization" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName
    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.beforeoptimize") $ show . pretty $ coreModule

    let optimizeModule = LVM_Syntax.coreModule2OptimizeModule coreModule

    if (CountingAnalysisAll `elem` options) || (CountingAnalysisOne `elem` options && isTopMostModule)
     then do
    {- Handle Counting Analysis after here -}
    --putStrLn "Solved =>"
    --putStrLn $ show $ Types.solveConstraints constraints
    --let optimizeModule' = countingAnalysis optimizeModule
        let wrapped_module = LVM_Syntax.wrap_module optimizeModule
        let constraints = LVM_Syntax.constraints wrapped_module
        --mapM (putStrLn . show . pretty) constraints

        let showIt = LVM_Syntax.showIt wrapped_module
        let letBangs = getLetBangs optimizeModule

        --putStrLn $ "Do counting analysis for: " ++ fullName
        mapM (putStrLn . show) {-print-} {-$ length $ show-} $ LVM_Syntax.filterShowIt showIt -- Shows the types of the functions and their corresponding top types
        -- {Important: This forces the typesystem on core}
        --putStrLn $ showLetBangs letBangs -- For comparison after added strictness
        let optimizeModule' = LVM_Syntax.optimizeModule wrapped_module
        --putStrLn $ "Done counting analysis for: " ++ fullName
        when (DumpCoreToFile `elem` options) $ do
            writeFile (fullNameNoExt ++ ".core.afteroptimize") $ show . pretty $ optimizeModule'
     else do
        putStrLn $ "Skip counting analysis for: " ++ fullName

    {- Back to normal coreModule -}
    let coreModule' = LVM_Syntax.optimizeModule2CoreModule optimizeModule

    return coreModule'
