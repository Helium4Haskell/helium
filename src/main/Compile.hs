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
import StaticErrors(errorsLogCode)

compile :: String -> [Option] -> [String] -> [String] -> IO ()
compile fullName options lvmPath doneModules =
    do
        let compileOptions = (options, fullName, doneModules)
        putStrLn ("Compiling " ++ fullName)

        -- Store the current module file-name and its context in
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName
        writeIORef refToCurrentImported doneModules

        contents <- safeReadFile fullName

        -- Phase 1: Lexing
        (lexerWarnings, tokens) <- 
            doPhaseWithExit 20 (const "L") compileOptions $
               phaseLexer fullName contents options
        
        unless (NoWarnings `elem` options) $
            showMessages lexerWarnings
        putStrLn("Finished lexing")
        -- Phase 2: Parsing
        parsedModule <-
            doPhaseWithExit 20 (const "P") compileOptions $
               phaseParser fullName tokens options
        putStrLn("Finished parsing")
        -- Phase 3: Importing
        (indirectionDecls, importEnvs) <-
            phaseImport fullName parsedModule lvmPath options
        putStrLn("Finished importing")
        -- Phase 4: Resolving operators
        resolvedModule <-
            doPhaseWithExit 20 (const "R") compileOptions $
               phaseResolveOperators parsedModule importEnvs options

        stopCompilingIf (StopAfterParser `elem` options)
        putStrLn("Resolving operators")
        -- putStrLn "Reached phase 5"

        -- Phase 5: Static checking
        (localEnv, typeSignatures, staticWarnings) <-
            doPhaseWithExit 20 (("S"++) . errorsLogCode) compileOptions $
               phaseStaticChecks fullName resolvedModule importEnvs options

        unless (NoWarnings `elem` options) $
            showMessages staticWarnings

        stopCompilingIf (StopAfterStaticAnalysis `elem` options)
        putStrLn("Static checks")
        -- putStrLn "Reached phase 6"
        -- Phase 6: Kind inferencing (by default turned off)
        let combinedEnv = foldr combineImportEnvironments localEnv importEnvs
        when (KindInferencing `elem` options) $
           doPhaseWithExit maximumNumberOfKindErrors (const "K") compileOptions $
              phaseKindInferencer combinedEnv resolvedModule options
        -- putStrLn "Reached phase 7"
        -- Phase 7: Type Inference Directives
        (beforeTypeInferEnv, typingStrategiesDecls) <-
            phaseTypingStrategies fullName combinedEnv typeSignatures options
        -- putStrLn "Reached phase 8"
        -- Phase 8: Type inferencing
        (dictionaryEnv, afterTypeInferEnv, toplevelTypes, typeWarnings) <-
            doPhaseWithExit maximumNumberOfTypeErrors (const "T") compileOptions $
               phaseTypeInferencer fullName resolvedModule {-doneModules-} localEnv beforeTypeInferEnv options

        unless (NoWarnings `elem` options) $
            showMessages typeWarnings

        stopCompilingIf (StopAfterTypeInferencing `elem` options)
        
        -- putStrLn "Reached phase 9"
        
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

        sendLog "C" fullName doneModules options

        let number = length staticWarnings + length typeWarnings + length lexerWarnings
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

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

maximumNumberOfKindErrors :: Int
maximumNumberOfKindErrors = 1