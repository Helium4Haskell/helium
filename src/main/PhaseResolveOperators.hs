module PhaseResolveOperators(phaseResolveOperators) where

import CompileUtils
import ResolveOperators(resolveOperators, operatorsFromModule)
import qualified PrettyPrinting(sem_Module)

phaseResolveOperators :: Module -> [ImportEnvironment] -> 
                            [Option] -> IO Module
phaseResolveOperators moduleBeforeResolve importEnvs options = do
    enterNewPhase "Resolving operators" options

    let importOperatorTable = operatorsFromModule moduleBeforeResolve
                           ++ concatMap operatorTable importEnvs
        (module_, resolveErrors) = 
                  resolveOperators importOperatorTable moduleBeforeResolve

    when (not (null resolveErrors)) $ do
        unless (NoLogging `elem` options) $ 
            logger "R" Nothing
        showErrorsAndExit resolveErrors 20 options

    when (DumpUHA `elem` options) $
        putStrLn $ show $ PrettyPrinting.sem_Module module_
    
    return module_

