module Compile where

import PhaseLexer
import PhaseParser
import PhaseImport
import PhaseResolveOperators
import PhaseStaticChecks
import PhaseTypingStrategies
import PhaseTypeInferencer
import PhaseDesugarer
import PhaseCodeGenerator
import CompileUtils
import Utils
import IOExts(writeIORef)

compile :: String -> [Option] -> [String] -> IO ()
compile fullName options doneModules =
    do
        putStrLn ("Compiling " ++ fullName)

        -- Store the current module file-name and its context in
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName
        writeIORef refToCurrentImported doneModules

        contents <- safeReadFile fullName

        -- Phase 1: Lexing
        (lexerWarnings, tokens) <- 
            phaseLexer fullName contents options
                        
        unless (NoWarnings `elem` options) $
            showMessages lexerWarnings

        -- Phase 2: Parsing
        parsedModule <- 
            phaseParser fullName tokens options

        -- Phase 3: Importing
        (indirectionDecls, importEnvs) <-
            phaseImport fullName parsedModule options
        
        -- Phase 4: Resolving operators
        resolvedModule <- 
            phaseResolveOperators parsedModule importEnvs options
            
        stopCompilingIf (StopAfterParser `elem` options)

        -- Phase 5: Static checking
        (localEnv, staticWarnings) <-
            phaseStaticChecks fullName resolvedModule importEnvs options        

        stopCompilingIf (StopAfterStaticAnalysis `elem` options)

        -- Phase 6: Typing Strategies
        (completeEnv, typingStrategiesDecls) <-
            phaseTypingStrategies fullName localEnv importEnvs options

        -- Phase 7: Type inferencing
        (finalEnv, toplevelTypes, typeWarnings) <- 
            phaseTypeInferencer fullName resolvedModule doneModules localEnv 
                                    importEnvs completeEnv options

        stopCompilingIf (StopAfterTypeInferencing `elem` options)

        -- Static Warnings
        let warnings = staticWarnings ++ typeWarnings

        unless (NoWarnings `elem` options) $
            showMessages warnings

        -- Phase 8: Desugaring
        coreModule <-                
            phaseDesugarer fullName resolvedModule 
                            (typingStrategiesDecls ++ indirectionDecls) 
                            finalEnv toplevelTypes options

        stopCompilingIf (StopAfterDesugar `elem` options)

        -- Phase 9: Code generation
        phaseCodeGenerator fullName coreModule options
        
        unless (NoLogging `elem` options) $ logger "C" Nothing

        let number = length warnings + length lexerWarnings
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
