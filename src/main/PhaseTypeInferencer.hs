module PhaseTypeInferencer (phaseTypeInferencer) where

import CompileUtils
import Warnings(Warning)
import qualified TypeInferencing(sem_Module)
import DictionaryEnvironment (DictionaryEnvironment)
import Types
import Data.FiniteMap
import UHA_Utils
import UHA_Syntax

phaseTypeInferencer :: 
    String -> Module -> [String] -> ImportEnvironment ->
        ImportEnvironment -> [Option] -> 
           IO ( DictionaryEnvironment,
               ImportEnvironment, 
               TypeEnvironment, [Warning])
phaseTypeInferencer fullName module_ doneModules localEnv beforeTypeInferEnv options = do
    enterNewPhase "Type inferencing" options

    -- 'W' and 'M' are predefined type inference algorithms
    let newOptions = (if AlgorithmW `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopLastPost, SolverGreedy]++) 
                        else id)
                   . (if AlgorithmM `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopFirstPre, SolverGreedy]++)  
                        else id)
                   $ options
    
        (debugIO, dictionaryEnv, _, _, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_
                beforeTypeInferEnv
                newOptions        
        
        -- add the top-level types (including the inferred types)
        afterTypeInferEnv = addToTypeEnvironment toplevelTypes beforeTypeInferEnv
    
    when (DumpTypeDebug `elem` options) debugIO      
    
    when (not (null typeErrors)) $ do
        when (DumpInformationForAllModules `elem` options) $
            putStr (show beforeTypeInferEnv)
        unless (NoLogging `elem` options) $ 
            sendLog "T" fullName doneModules options
        showErrorsAndExit (reverse typeErrors) maximumNumberOfTypeErrors options

    -- Dump information
    if (DumpInformationForAllModules `elem` options)
      then
         putStrLn (show afterTypeInferEnv)
      else if (DumpInformationForThisModule `elem` options)
             then
                putStrLn (show (addToTypeEnvironment toplevelTypes localEnv))
             else
                return ()

    return (dictionaryEnv, afterTypeInferEnv, toplevelTypes, warnings)

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3
