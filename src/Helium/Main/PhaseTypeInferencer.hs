{-| Module      :  PhaseTypeInferencer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}
module Helium.Main.PhaseTypeInferencer (phaseTypeInferencer) where

import Helium.Main.CompileUtils
import Helium.StaticAnalysis.Messages.Warnings(Warning)
import Helium.StaticAnalysis.Inferencers.TypeInferencing(typeInferencing)
import Helium.StaticAnalysis.Inferencers.OutsideInX.TypeInferencing(typeInferencingIOX)
import Helium.ModuleSystem.DictionaryEnvironment (DictionaryEnvironment)
import Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion
--import UHA_Syntax
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Information (showInformation)
import Helium.StaticAnalysis.Messages.HeliumMessages
import System.FilePath.Posix
import Data.Maybe
import qualified Data.Map.Strict as M
import Helium.Utils.Utils
import Debug.Trace

phaseTypeInferencer :: 
    String -> String -> Module -> ImportEnvironment -> ImportEnvironment -> [Option] -> 
    Phase TypeError (DictionaryEnvironment, ImportEnvironment, TypeEnvironment, [Warning])

phaseTypeInferencer basedir fullName module_ localEnv completeEnv options = 
   do
      enterNewPhase "Type inferencing" options
   
      -- 'W' and 'M' are predefined type inference algorithms
      let newOptions = (if AlgorithmW `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopLastPost, SolverGreedy]++) 
                        else id)
                   . (if AlgorithmM `elem` options
                        then filter (/= NoSpreading) . ([TreeWalkInorderTopFirstPre, SolverGreedy]++)  
                        else id)
                   $ options
      let outsideInResult = if OutsideInX `elem` options then   
               Just $ typeInferencingIOX newOptions completeEnv module_
            else
               Nothing
      
      let (debugIO, dictionaryEnv, toplevelTypes, typeErrors, warnings) =
           typeInferencing newOptions completeEnv module_

        -- add the top-level types (including the inferred types)
      let finalEnv = addToTypeEnvironment toplevelTypes completeEnv
    
      when (DumpTypeDebug `elem` options) debugIO      
     
      -- display name information
      showInformation True options finalEnv
      when (VerifyOutsideInResult `elem` options) 
         (
            do
               let err = internalError "PhaseTyperInferencer" "phaseTypeInferencer" "Flag VerifyOutsideInResult used without OutsideInX flag present"
               let (dictionaryEnvOIX, toplevelTypesOIX, typeErrorsOIX, warningOIX, gadtUsed) = fromMaybe err outsideInResult
               let tld = tpSchemeListDifference toplevelTypes toplevelTypesOIX
               --unless (dictionaryEnv == dictionaryEnvOIX) (
                 -- do
                    -- putStrLn "Dictionary environment are not equal"
                     --print dictionaryEnv
                     --print dictionaryEnvOIX
                 -- )
               unless (not (null typeErrorsOIX) && null tld) (
                  do
                     if null tld then return () else do
                        putStrLn "Top level types are not equal"
                        putStrLn (unlines $ map show $ M.toList tld)
                        putStrLn (show toplevelTypes)
                        putStrLn (show toplevelTypesOIX)
                  )    
               when gadtUsed (
                  do 
                     putStrLn (show toplevelTypesOIX)
                     putStrLn (sortAndShowMessages typeErrorsOIX)
                  )   
               --putStrLn $ unlines $ map show $ M.toList toplevelTypes
               unless (null typeErrorsOIX) ( do
                     --putStrLn (sortAndShowMessages typeErrorsOIX)
                     return ()
                  )
               unless (null typeErrors && null typeErrorsOIX || not (null typeErrors) && not (null typeErrorsOIX)) (
                  do
                     putStrLn "Length of errors doesn't match"
                     putStrLn (sortAndShowMessages typeErrorsOIX)
                     putStrLn (show toplevelTypes)
                     print (show toplevelTypesOIX)
                     
                  )
                       
         )

      case typeErrors of 
         _:_ ->
            do when (DumpInformationForAllModules `elem` options) $ putStr (show completeEnv)
               return (Left typeErrors)
          
         [] -> 
            do -- Dump information
               when (DumpInformationForAllModules `elem` options) $ 
                  print finalEnv
               when (HFullQualification `elem` options) $
                  writeFile (combinePathAndFile basedir (dropExtension $ takeFileName fullName) ++ ".fqn") 
                           (holmesShowImpEnv module_ finalEnv)
               when (  DumpInformationForThisModule `elem` options 
                     && DumpInformationForAllModules `notElem` options
                     ) 
                     $ print (addToTypeEnvironment toplevelTypes localEnv)
                     
               return (Right (dictionaryEnv, finalEnv, toplevelTypes, warnings))