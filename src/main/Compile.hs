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
        (lexerWarnings, tokens) <- 
            phaseLexer fullName doneModules contents options
                        
        unless (NoWarnings `elem` options) $
            showMessages lexerWarnings

        -- Phase 2: Parsing
        parsedModule <- 
            phaseParser fullName doneModules tokens options

        -- Phase 3: Importing
        (indirectionDecls, importEnvs) <-
            phaseImport fullName parsedModule lvmPath options
        
        -- Phase 4: Resolving operators
        resolvedModule <- 
            phaseResolveOperators fullName doneModules parsedModule importEnvs options
            
        stopCompilingIf (StopAfterParser `elem` options)

        -- Phase 5: Static checking
        (localEnv, staticWarnings) <-
            phaseStaticChecks fullName doneModules resolvedModule importEnvs options        

        unless (NoWarnings `elem` options) $
            showMessages staticWarnings

        stopCompilingIf (StopAfterStaticAnalysis `elem` options)

        -- Phase 6: Typing Strategies
        (completeEnv, typingStrategiesDecls) <-
            phaseTypingStrategies fullName localEnv importEnvs options

        -- Phase 7: Type inferencing
        (finalEnv, inferredTypes, toplevelTypes, typeWarnings) <- 
            phaseTypeInferencer fullName resolvedModule doneModules localEnv 
                                    importEnvs completeEnv options

        unless (NoWarnings `elem` options) $
            showMessages typeWarnings

        stopCompilingIf (StopAfterTypeInferencing `elem` options)

        -- Phase 8: Desugaring
        coreModule <-                
            phaseDesugarer fullName resolvedModule 
                            (typingStrategiesDecls ++ indirectionDecls) 
                            finalEnv inferredTypes toplevelTypes options

        stopCompilingIf (StopAfterDesugar `elem` options)

        -- Phase 9: Code generation
        phaseCodeGenerator fullName coreModule options
        
        unless (NoLogging `elem` options) $ 
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
