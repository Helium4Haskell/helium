module PhaseTypeInferencer (phaseTypeInferencer) where

import CompileUtils
import Tree(flattenM, flattenW)
import Warnings(Warning)
import qualified TypeInferencing(sem_Module)

import Types -- temporary
import FiniteMap
import UHA_Utils
import UHA_Syntax

phaseTypeInferencer :: 
    String -> Module -> [String] -> ImportEnvironment -> [ImportEnvironment] -> 
        ImportEnvironment -> [Option] -> 
           IO (ImportEnvironment, FiniteMap NameWithRange TpScheme  {- == LocalTypes -}, TypeEnvironment, [Warning])
phaseTypeInferencer fullName module_ doneModules localEnv importEnvs completeEnv options = do
    enterNewPhase "Type inferencing" options

    let (strategy,useTypeGraph)
            | AlgorithmW `elem` options = (flattenW,False)
            | AlgorithmM `elem` options = (flattenM,False)
            | otherwise                 = (flattenW,True ) -- default algorithm W + TypeGraphs

        (debugTypes, localTypes, overloadedVars, _, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_
                strategy
                (adjustIE completeEnv)                
                useTypeGraph        
        
        -- add the top-level types (including the inferred types)
        finalEnv = addToTypeEnvironment toplevelTypes completeEnv
    
    putStrLn (unlines ("" : "toplevelTypes: " : map (\(n,ts) -> show n ++ " :: "++show (getQualifiedType ts)) (fmToList toplevelTypes)))
    putStrLn (unlines ("" : "localTypes:" : map show (fmToList localTypes)))
    putStrLn (unlines ("" : "overloadedVars:"   : map (\(n,(m,t)) -> show n ++ " in scope of " ++ show m ++" has type " ++ show t) (fmToList overloadedVars)))
    
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

    return (finalEnv, localTypes, toplevelTypes, warnings)

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

-- temporary: for testing type classes --> also remove extra imports
adjustIE :: ImportEnvironment -> ImportEnvironment
adjustIE x = setTypeEnvironment (adjustTE (typeEnvironment x)) x

adjustTE :: FiniteMap Name TpScheme -> FiniteMap Name TpScheme
adjustTE fm = let op (s,ts) fm = addToFM fm (nameFromString s) ts 
              in foldr op fm list
              
  where
   list = [ ("showString", generalize [] [Predicate "Show" (TVar 0)] (TVar 0 .->. stringType))
          , ("=="        , generalize [] [Predicate "Eq"   (TVar 0)] (TVar 0 .->. TVar 0 .->. boolType))
          , ("<"         , generalize [] [Predicate "Ord"  (TVar 0)] (TVar 0 .->. TVar 0 .->. boolType))
          ]
        
