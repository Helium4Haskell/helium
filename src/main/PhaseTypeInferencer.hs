module PhaseTypeInferencer(phaseTypeInferencer) where

import CompileUtils
import Strategy(algM, algW)
import Warnings(Warning)
import qualified TypeInferencing(sem_Module)

phaseTypeInferencer :: 
    String -> Module -> [String] -> ImportEnvironment -> [ImportEnvironment] -> 
        ImportEnvironment -> [Option] -> IO (ImportEnvironment, TypeEnvironment, [Warning])
phaseTypeInferencer fullName module_ doneModules localEnv importEnvs completeEnv options = do
    enterNewPhase "Type inferencing" options

    let (strategy,useTypeGraph)
            | AlgorithmW `elem` options = (algW,False)
            | AlgorithmM `elem` options = (algM,False)
            | otherwise                 = (algW,True ) -- default algorithm W + TypeGraphs

        (debugTypes, _, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_
                completeEnv
                strategy
                useTypeGraph

        -- add the top-level types (including the inferred types)
        finalEnv = addToTypeEnvironment toplevelTypes completeEnv

    when (DumpTypeDebug `elem` options) debugTypes
    
    when (not (null typeErrors)) $ do
        when (DumpInformationForAllModules `elem` options) $
            putStr (show (foldr combineImportEnvironments emptyEnvironment importEnvs)) 
        unless (NoLogging `elem` options) $ 
            sendLog "T" fullName doneModules options
        showErrorsAndExit (reverse typeErrors) maximumNumberOfTypeErrors options

    -- Dump information
    if (DumpInformationForAllModules `elem` options)
      then
         putStrLn (show finalEnv)
      else if (DumpInformationForThisModule `elem` options)
             then
                putStrLn (show (addToTypeEnvironment toplevelTypes localEnv))
             else
                return ()

    return (finalEnv, toplevelTypes, warnings)

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3


