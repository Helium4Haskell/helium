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
    let showIt = LVM_Syntax.showIt optimizeModule
    let letBangs = getLetBangs optimizeModule
    if (CountingAnalysisAll `elem` options) || (CountingAnalysisOne `elem` options && isTopMostModule)
     then do
    {- Handle Counting Analysis after here -}
    --let constraints = LVM_Syntax.constraints optimizeModule
    --putStrLn $ show $ constraints
    --putStrLn "Solved =>"
    --putStrLn $ show $ Types.solveConstraints constraints
    --let optimizeModule' = countingAnalysis optimizeModule
        putStrLn $ "Do counting analysis for: " ++ fullName
        print $ length $ show showIt -- Shows the types of the functions and their corresponding top types
        -- {Important: This forces the typesystem on core}
        --putStrLn $ showLetBangs letBangs -- For comparison after added strictness
        putStrLn $ "Done counting analysis for: " ++ fullName
     else do
        putStrLn $ "Skip counting analysis for: " ++ fullName

    {- Back to normal coreModule -}
    let coreModule' = LVM_Syntax.optimizeModule2CoreModule optimizeModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core.afteroptimize") $ show . pretty $ coreModule'

    return coreModule'
