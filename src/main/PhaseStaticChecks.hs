module PhaseStaticChecks(phaseStaticChecks) where

import CompileUtils
import Warnings(Warning)
import StaticErrors(errorsLogCode)
import qualified StaticChecks(sem_Module)

phaseStaticChecks :: String -> Module -> [ImportEnvironment] -> 
                        [Option] -> IO (ImportEnvironment, [Warning])
phaseStaticChecks fullName module_ importEnvs options = do
    enterNewPhase "Static checking" options

    let (_, baseName, _) = splitFilePath fullName

        (localEnv, errors, warnings) =
            StaticChecks.sem_Module module_ baseName importEnvs

    when (not (null errors)) $ do
        when (DumpInformationForAllModules `elem` options) $
            putStrLn (show (foldr combineImportEnvironments 
                emptyEnvironment importEnvs))
        unless (NoLogging `elem` options) $ 
            logger ("S"++errorsLogCode errors) Nothing
        showErrorsAndExit errors 20 options
    
    return (localEnv, warnings)

