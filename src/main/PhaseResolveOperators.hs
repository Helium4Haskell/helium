module PhaseResolveOperators(phaseResolveOperators) where

import CompileUtils
import ResolveOperators(resolveOperators, operatorsFromModule)
import qualified PrettyPrinting(sem_Module)
import Data.FiniteMap

phaseResolveOperators :: String -> [String] -> Module -> [ImportEnvironment] -> 
                            [Option] -> IO Module
phaseResolveOperators fullName doneModules moduleBeforeResolve importEnvs options = do
    enterNewPhase "Resolving operators" options

    let importOperatorTable = 
            foldr1 plusFM ( operatorsFromModule moduleBeforeResolve
                          : map operatorTable importEnvs
                          )
        (module_, resolveErrors) = 
                  resolveOperators importOperatorTable moduleBeforeResolve

    when (not (null resolveErrors)) $ do
        unless (NoLogging `elem` options) $ 
            sendLog "R" fullName doneModules options
        showErrorsAndExit resolveErrors 20 options

    when (DumpUHA `elem` options) $
        putStrLn $ show $ PrettyPrinting.sem_Module module_
    
    return module_

