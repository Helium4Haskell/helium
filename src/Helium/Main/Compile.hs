{-| Module      :  Compile
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.Compile(compile, readCore) where

import Lvm.Core.Expr(CoreModule)
import qualified Lvm.Core.Parsing.Parser as Lvm
import qualified Lvm.Core.Parsing.Lexer as Lvm
import qualified Lvm.Core.Parsing.Layout as Lvm
import qualified Lvm.Core.Module as Lvm
import qualified Lvm.Core.Expr as Lvm
import qualified Lvm.Import as Lvm
import Lvm.Path (searchPath, searchPathMaybe)
import Lvm.Common.Id (Id, stringFromId)
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
import qualified Helium.CodeGeneration.Iridium.Parse.Module as Iridium
import qualified Helium.CodeGeneration.Iridium.ResolveDependencies as Iridium
import Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule)
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

    (iridiumFiles, shouldLink, warnings) <- if ext /= "iridium" then do
        (coreModule, warnings) <- case ext of
          "hs" -> compileHaskellToCore basedir fullName contents options lvmPath doneModules
          "core" -> do
            let tokens = Lvm.layout $ Lvm.lexer (1,1) contents
            -- coreModule <- Lvm.parseModule fullName tokens
            (m, implExps, es) <- Lvm.parseModuleExport fullName tokens

            -- resolve imports
            chasedMod  <- Lvm.lvmImport (searchPath lvmPath ".lvm" . stringFromId) m
            let publicmod = Lvm.modulePublic implExps es chasedMod
            return (publicmod, 0)
          _ -> do
            putStrLn $ "Unsupported file extension: " ++ show ext
            exitWith (ExitFailure 1)

        -- Phase 10: Code generation
        phaseCodeGenerator fullName coreModule options

        sendLog "C" fullName doneModules options

        -- Phase 11: Code generation for Iridium
        (files, link) <- phaseCodeGeneratorIridium lvmPath fullName coreModule options
        return (files, link, warnings)
      else do
        iridium <- case Iridium.parseModule contents of
            Left err -> do
                putStrLn $ "Failed to parse Iridium file " ++ show fullName
                print err
                exitWith (ExitFailure 1)
            Right ir -> return ir
        print iridium
        return ([Iridium.IridiumFile fullName iridium True], False, 0)

    -- Phase 12: Generate LLVM code
    phaseCodeGeneratorLlvm iridiumFiles shouldLink options

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

resolveDeclarations :: [String] -> Id -> IO (Lvm.CoreModule)
resolveDeclarations paths name = do
  maybeFullNameLvm <- searchPathMaybe paths ".lvm" $ stringFromId name
  case maybeFullNameLvm of
    Just fullName -> do
      readCore fullName
    Nothing -> do
      fullName <- searchPath paths ".iridium" $ stringFromId name
      contents <- readSourceFile fullName
      iridium <- case Iridium.parseModule contents of
        Left err -> do
            putStrLn $ "Failed to parse Iridium file " ++ show fullName
            print err
            exitWith (ExitFailure 1)
        Right ir -> return ir
      return $ toAbstractModule iridium

readCore :: FilePath -> IO Lvm.CoreModule
readCore fullName = do
    contents <- readSourceFile fullName
    let tokens = Lvm.layout $ Lvm.lexer (1,1) contents
    Lvm.parseModule fullName tokens
