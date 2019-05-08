{-| Module      :  Compile
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.Compile where

import Helium.Main.PhaseLexer
import Helium.Main.PhaseParser
import Helium.Main.PhaseImport
import Helium.Main.PhaseResolveOperators
import Helium.Main.PhaseStaticChecks
import Helium.Main.PhaseKindInferencer
import Helium.Main.PhaseTypingStrategies
import Helium.Main.PhaseTypeInferencer
import Helium.Main.PhaseDesugarer
import Helium.Main.PhaseCodeGenerator
import Helium.Main.CompileUtils
import Helium.Main.Args (overloadingFromOptions)
import Helium.Utils.Utils
import Data.IORef
import Helium.StaticAnalysis.Messages.StaticErrors(errorsLogCode)

compile :: String -> String -> [Option] -> [String] -> [String] -> IO ()
compile basedir fullName options lvmPath doneModules =
    do
        let compileOptions = (options, fullName, doneModules)
        putStrLn ("Compiling " ++ fullName)

        -- Store the current module file-name and its context in
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName
        writeIORef refToCurrentImported doneModules

        contents <- readSourceFile fullName

        -- Phase 1: Lexing
        -- putStrLn "===== Phase 1 ====="
        (lexerWarnings, tokens) <-
            doPhaseWithExit 20 (const "L") compileOptions $
               phaseLexer fullName contents options

        unless (NoWarnings `elem` options) $
            showMessages lexerWarnings


        -- Phase 2: Parsing
        -- putStrLn "===== Phase 2 ====="
        parsedModule <-
            doPhaseWithExit 20 (const "P") compileOptions $
               phaseParser fullName tokens options

        -- Phase 3: Importing
        -- putStrLn "===== Phase 3 ====="
        (indirectionDecls, importEnvsWithMod) <-
            phaseImport fullName parsedModule lvmPath options
        let importEnvs = map (\(_,b,_) -> b) importEnvsWithMod
        
        -- Phase 4: Resolving operators
        -- putStrLn "===== Phase 4 ====="
        resolvedModule <-
            doPhaseWithExit 20 (const "R") compileOptions $
               phaseResolveOperators parsedModule importEnvs options

        stopCompilingIf (StopAfterParser `elem` options)

        -- Phase 5: Static checking
        -- putStrLn "===== Phase 5 ====="
        (localEnv, typeSignatures, staticWarnings) <-
            doPhaseWithExit 20 (("S"++) . errorsLogCode) compileOptions $
               phaseStaticChecks fullName resolvedModule importEnvsWithMod options    

               
        unless (NoWarnings `elem` options) $
            showMessages staticWarnings

        stopCompilingIf (StopAfterStaticAnalysis `elem` options)

        -- Phase 6: Kind inferencing (by default turned off)
        -- putStrLn "===== Phase 6 ====="
        let combinedEnv = combineImportEnvironmentList (localEnv:importEnvs)
        when (KindInferencing `elem` options) $
           doPhaseWithExit maximumNumberOfKindErrors (const "K") compileOptions $
              phaseKindInferencer combinedEnv resolvedModule options

        -- Phase 7: Type Inference Directives
        -- putStrLn "===== Phase 7 ====="
        (beforeTypeInferEnv, typingStrategiesDecls) <-
            phaseTypingStrategies fullName combinedEnv typeSignatures options

        -- print beforeTypeInferEnv

        -- Phase 8: Type inferencing
        -- putStrLn "===== Phase 8 ====="
        (dictionaryEnv, afterTypeInferEnv, toplevelTypes, typeWarnings) <-
            doPhaseWithExit maximumNumberOfTypeErrors (const "T") compileOptions $
               phaseTypeInferencer basedir fullName resolvedModule {-doneModules-} localEnv beforeTypeInferEnv options

        unless (NoWarnings `elem` options) $
            showMessages typeWarnings

        stopCompilingIf (StopAfterTypeInferencing `elem` options)

        -- Phase 9: Desugaring
        -- putStrLn "===== Phase 9 ====="
        coreModule <-
            phaseDesugarer dictionaryEnv
                           fullName resolvedModule
                           (typingStrategiesDecls ++ indirectionDecls)
                           afterTypeInferEnv
                           toplevelTypes
                           options

        stopCompilingIf (StopAfterDesugar `elem` options)

        -- Phase 10: Code generation
        -- putStrLn "===== Phase 10 ====="
        phaseCodeGenerator fullName coreModule options

        sendLog "C" fullName doneModules options

        let number = length staticWarnings + length typeWarnings + length lexerWarnings
        putStrLn $ "Compilation successful" ++
                      if number == 0 || (NoWarnings `elem` options)
                        then ""
                        else " with " ++ show number ++ " warning" ++ if number == 1 then "" else "s"

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (exitWith (ExitFailure 1))

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

maximumNumberOfKindErrors :: Int
maximumNumberOfKindErrors = 1