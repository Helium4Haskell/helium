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
phaseTypeInferencer fullName module_ doneModules localEnv completeEnv options = do
    enterNewPhase "Type inferencing" options

    -- 'W' and 'M' are predefined type inference algorithms
    let newOptions = (if AlgorithmW `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopLastPost, SolverGreedy]++) 
                        else id)
                   . (if AlgorithmM `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopFirstPre, SolverGreedy]++)  
                        else id)
                   $ options
    
        (debugIO, dictionaryEnv, localTypes, _, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_
                completeEnv
                newOptions        
        
        -- add the top-level types (including the inferred types)
        finalEnv = addToTypeEnvironment toplevelTypes completeEnv
        inferredTypes = addListToFM localTypes 
                [ (NameWithRange name, ts) | (name, ts) <- fmToList (typeEnvironment finalEnv) ]
    
    when (DumpTypeDebug `elem` options) debugIO      
    
{-
    putStrLn (unlines ("" : "toplevelTypes: " : map (\(n,ts) -> show (NameWithRange n) ++ " :: "++show (getQualifiedType ts)) (fmToList toplevelTypes)))
    putStrLn (unlines ("" : "localTypes:" : map show (fmToList localTypes)))
    putStrLn (unlines ("" : "overloadedVars:"   : map (\(n,(m,t)) -> show n ++ " in scope of " ++ show m ++" has type " ++ show t) (fmToList overloadedVars)))        
-}

    when (not (null typeErrors)) $ do
        when (DumpInformationForAllModules `elem` options) $
            putStr (show completeEnv)
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

    return (dictionaryEnv, finalEnv, toplevelTypes, warnings)

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3
