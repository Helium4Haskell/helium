{-| Module      :  Compile
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.Compile where

import Lvm.Core.Expr(CoreModule)
import qualified Lvm.Core.Parsing.Parser as Lvm
import qualified Lvm.Core.Parsing.Lexer as Lvm
import qualified Lvm.Core.Parsing.Layout as Lvm
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
import Helium.Main.PhaseCodeGeneratorIridium
import Helium.Main.PhaseCodeGeneratorLlvm
import Helium.Main.CompileUtils
import Helium.Parser.Lexer (checkTokenStreamForClassOrInstance)
import Helium.Main.Args (overloadingFromOptions)
import Helium.Utils.Utils
import Data.IORef
import Helium.StaticAnalysis.Messages.StaticErrors(errorsLogCode)
import System.Exit

compile :: String -> String -> [Option] -> [String] -> [String] -> IO ()
compile basedir fullName options lvmPath doneModules =
  do
    putStrLn ("Compiling " ++ fullName)
    let (_, _, ext) = splitFilePath fullName

    -- Store the current module file-name and its context in
    -- two IO refs (unsafe! only used for internal error bug-report)
    writeIORef refToCurrentFileName fullName
    writeIORef refToCurrentImported doneModules

    contents <- readSourceFile fullName

    (coreModule, warnings) <- case ext of
      "hs" -> compileHaskellToCore basedir fullName contents options lvmPath doneModules
      "core" -> do
        let tokens = Lvm.layout (Lvm.lexer (1,1) contents)
        coreModule <- Lvm.parseModule fullName tokens
        return (coreModule, 0)
      _ -> do
        putStrLn $ "Unsupported file extension: " ++ show ext
        exitWith (ExitFailure 1)

    -- Phase 10: Code generation
    phaseCodeGenerator fullName coreModule options
    
    sendLog "C" fullName doneModules options

    -- Phase 11: Code generation for Iridium
    (files, shouldLink) <- phaseCodeGeneratorIridium lvmPath fullName coreModule options

    putStrLn $ "Compilation successful" ++
                  if warnings == 0 || (NoWarnings `elem` options)
                    then ""
                    else " with " ++ show warnings ++ " warning" ++ if warnings == 1 then "" else "s"

compileHaskellToCore :: String -> String -> String -> [Option] -> [String] -> [String] -> IO (CoreModule, Int)
compileHaskellToCore basedir fullName contents options lvmPath doneModules = do
  let compileOptions = (options, fullName, doneModules)

  -- Phase 1: Lexing
  (lexerWarnings, tokens) <- 
      doPhaseWithExit 20 (const "L") compileOptions $
          phaseLexer fullName contents options

  unless (NoWarnings `elem` options) $
      showMessages lexerWarnings

  -- If the token stream contains the words class or instance
  -- and overloading is off, then print error message and bail out:
  if not (overloadingFromOptions options) then 
    let classInstanceMessages = checkTokenStreamForClassOrInstance tokens
    in if not (null classInstanceMessages) 
        then do 
              showMessages classInstanceMessages
              stopCompilingIf True
        else return ()
  else
    return ()

  -- Phase 2: Parsing
  parsedModule <- 
    doPhaseWithExit 20 (const "P") compileOptions $
      phaseParser fullName tokens options

  -- Phase 3: Importing
  (indirectionDecls, importEnvs) <-
      phaseImport fullName parsedModule lvmPath options
  
  -- Phase 4: Resolving operators
  resolvedModule <- 
      doPhaseWithExit 20 (const "R") compileOptions $
          phaseResolveOperators parsedModule importEnvs options
      
  stopCompilingIf (StopAfterParser `elem` options)

  -- Phase 5: Static checking
  (localEnv, typeSignatures, staticWarnings) <-
      doPhaseWithExit 20 (("S"++) . errorsLogCode) compileOptions $
          phaseStaticChecks fullName resolvedModule importEnvs options        

  unless (NoWarnings `elem` options) $
      showMessages staticWarnings

  stopCompilingIf (StopAfterStaticAnalysis `elem` options)

  -- Phase 6: Kind inferencing (by default turned off)
  let combinedEnv = foldr combineImportEnvironments localEnv importEnvs
  when (KindInferencing `elem` options) $
      doPhaseWithExit maximumNumberOfKindErrors (const "K") compileOptions $
        phaseKindInferencer combinedEnv resolvedModule options

  -- Phase 7: Type Inference Directives
  (beforeTypeInferEnv, typingStrategiesDecls) <-
      phaseTypingStrategies fullName combinedEnv typeSignatures options

  -- Phase 8: Type inferencing
  (dictionaryEnv, afterTypeInferEnv, toplevelTypes, typeWarnings) <- 
      doPhaseWithExit maximumNumberOfTypeErrors (const "T") compileOptions $ 
          phaseTypeInferencer basedir fullName resolvedModule {-doneModules-} localEnv beforeTypeInferEnv options

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

  let number = length staticWarnings + length typeWarnings + length lexerWarnings
  return (coreModule, number)

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (exitWith (ExitFailure 1))

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

maximumNumberOfKindErrors :: Int
maximumNumberOfKindErrors = 1