{-| Module      :  Compile
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Compile where

import PhaseLexer
import PhaseParser
import PhaseImport
import PhaseResolveOperators
import PhaseStaticChecks
import PhaseKindInferencer
import PhaseTypingStrategies
import PhaseTypeInferencer
import PhaseDesugarer
import PhaseCodeGenerator
import CompileUtils
import Utils
import Data.IORef

compile :: String -> [Option] -> [String] -> [String] -> IO ()
compile fullName options lvmPath doneModules =
    do
        putStrLn ("Compiling " ++ fullName)

        -- Store the current module file-name and its context in
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName
        writeIORef refToCurrentImported doneModules

        contents <- safeReadFile fullName

        -- Phase 1: Lexing
        (lexerBeforeWarnings, lexerAfterWarnings, tokens) <- 
            phaseLexer fullName doneModules contents options
        
        unless (NoWarnings `elem` options) $
            showMessages lexerBeforeWarnings

        -- Phase 2: Parsing
        parsedModule <- 
            phaseParser fullName doneModules tokens options

        unless (NoWarnings `elem` options) $
            showMessages lexerAfterWarnings

        -- Phase 3: Importing
        (indirectionDecls, importEnvs) <-
            phaseImport fullName parsedModule lvmPath options
        
        -- Phase 4: Resolving operators
        resolvedModule <- 
            phaseResolveOperators fullName doneModules parsedModule importEnvs options
            
        stopCompilingIf (StopAfterParser `elem` options)

        -- Phase 5: Static checking
        (localEnv, typeSignatures, staticWarnings) <-
            phaseStaticChecks fullName doneModules resolvedModule importEnvs options        

        unless (NoWarnings `elem` options) $
            showMessages staticWarnings

        stopCompilingIf (StopAfterStaticAnalysis `elem` options)

        -- Phase 6: Kind inferencing (by default turned off)
        let combinedEnv = foldr combineImportEnvironments localEnv importEnvs
        when (KindInferencing `elem` options) $
           phaseKindInferencer combinedEnv resolvedModule options
        
        -- Phase 7: Type Inference Directives
        (beforeTypeInferEnv, typingStrategiesDecls) <-
            phaseTypingStrategies fullName combinedEnv typeSignatures options

        -- Phase 8: Type inferencing
        (dictionaryEnv, afterTypeInferEnv, toplevelTypes, typeWarnings) <- 
            phaseTypeInferencer fullName resolvedModule doneModules localEnv 
                                    beforeTypeInferEnv options

        unless (NoWarnings `elem` options) $
            showMessages typeWarnings

        stopCompilingIf (StopAfterTypeInferencing `elem` options)

        -- Phase 9: Desugaring
        coreModule <-                
            phaseDesugarer dictionaryEnv
                           fullName resolvedModule 
                           (typingStrategiesDecls ++ indirectionDecls) 
                           afterTypeInferEnv
                           toplevelTypes 
                           options                           

        stopCompilingIf (StopAfterDesugar `elem` options)

        -- Phase 10: Code generation
        phaseCodeGenerator fullName coreModule options
        
        unless (NoLogging `elem` options) $ 
            sendLog "C" fullName doneModules options

        let number = length staticWarnings + length typeWarnings + length lexerBeforeWarnings + length lexerAfterWarnings
        putStrLn $ "Compilation successful" ++
                      if number == 0 || (NoWarnings `elem` options)
                        then ""
                        else " with " ++ show number ++ " warning" ++ if number == 1 then "" else "s"

safeReadFile :: String -> IO String
safeReadFile fullName = 
    catch 
        (readFile fullName)
        (\ioError -> 
            let message = "Unable to read file " ++ show fullName 
                       ++ " (" ++ show ioError ++ ")"
            in throw message)

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (exitWith (ExitFailure 1))
