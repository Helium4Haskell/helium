module PhaseTypeInferencer (phaseTypeInferencer) where

import CompileUtils
import Tree(flattenM, flattenW)
import Warnings(Warning)
import qualified TypeInferencing(sem_Module)

import Types -- temporary
import Data.FiniteMap
import UHA_Utils
import UHA_Syntax

phaseTypeInferencer :: 
    String -> Module -> [String] -> ImportEnvironment ->
        ImportEnvironment -> [Option] -> 
           IO (ImportEnvironment, FiniteMap NameWithRange TpScheme  {- == LocalTypes -}, 
               FiniteMap NameWithRange (NameWithRange, QType) {- OverloadedVariables -}, TypeEnvironment, [Warning])
phaseTypeInferencer fullName module_ doneModules localEnv completeEnv options = do
    enterNewPhase "Type inferencing" options

    let (debugIO, localTypes, overloadedVars, _, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_
                completeEnv
                options        
        
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

    return (finalEnv, inferredTypes, overloadedVars, toplevelTypes, warnings)

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3
