{-| Module      :  Compile
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.Compile(compile) where

import Helium.Lvm.Core.Expr(CoreModule)
import qualified Helium.Lvm.Core.Parsing.Parser as Lvm
import qualified Helium.Lvm.Core.Parsing.Lexer as Lvm
import qualified Helium.Lvm.Core.Parsing.Layout as Lvm
import qualified Helium.Lvm.Core.Module as Lvm
import qualified Helium.Lvm.Core.Expr as Lvm
import qualified Helium.Lvm.Import as Lvm
import Helium.Lvm.Path (searchPath, searchPathMaybe)
import Helium.Lvm.Common.Id (Id, stringFromId, newNameSupply, splitNameSupply)
import Helium.Main.PhaseLexer
import Helium.Main.PhaseParser
import Helium.Main.PhaseImport
import Helium.Main.PhaseResolveOperators
import Helium.Main.PhaseStaticChecks
import Helium.Main.PhaseKindInferencer
import Helium.Main.PhaseTypingStrategies
import Helium.Main.PhaseTypeInferencer
import Helium.Main.PhaseDesugarer
import Helium.Main.PhaseCodeGeneratorIridium
import Helium.Main.PhaseCodeGeneratorLlvm
import Helium.Main.CompileUtils
import qualified Helium.CodeGeneration.Core.TypeCheck as Core
import qualified Helium.CodeGeneration.Iridium.Parse.Module as Iridium
import qualified Helium.CodeGeneration.Iridium.ResolveDependencies as Iridium
import qualified Helium.CodeGeneration.Iridium.FileCache as Iridium
import Helium.CodeGeneration.Iridium.ImportAbstract (toAbstractModule)
import Helium.Main.Args (overloadingFromOptions)
import Helium.Utils.Utils
import Data.IORef
import Helium.StaticAnalysis.Messages.StaticErrors(errorsLogCode)
import System.FilePath(joinPath)
import System.Exit

-- Temp fix to add types to imported declarations
import Helium.CodeGeneration.CoreUtils
import Helium.Syntax.UHA_Utils
import qualified Data.Map as M
import Data.Maybe

import Text.PrettyPrint.Leijen (pretty)

compile :: String -> String -> [Option] -> [String] -> Iridium.FileCache -> [String] -> IO ()
compile basedir fullName options lvmPath iridiumCache doneModules =
  do
    putStrLn ("Compiling " ++ fullName)
    let (filePath, fileName, ext) = splitFilePath fullName

    -- Store the current module file-name and its context in
    -- two IO refs (unsafe! only used for internal error bug-report)
    writeIORef refToCurrentFileName fullName
    writeIORef refToCurrentImported doneModules

    contents <- readSourceFile fullName

    supply <- newNameSupply
    let (supplyIridium, supplyLlvm) = splitNameSupply supply

    (iridiumFiles, shouldLink, warnings) <- if ext /= "iridium" then do
        (coreModule, warnings) <- case ext of
          "hs" -> compileHaskellToCore basedir fullName contents options iridiumCache doneModules
          "core" -> do
            let tokens = Lvm.layout $ Lvm.lexer (1,1) contents
            m <- Lvm.parseModule fullName tokens

            -- resolve imports
            publicmod <- Lvm.lvmImport (resolveDeclarations iridiumCache) m

            verifyCore options "LvmImport" publicmod

            return (publicmod, 0)
          _ -> do
            putStrLn $ "Unsupported file extension: " ++ show ext
            exitWith (ExitFailure 1)

        -- Phase 10: Code generation for Iridium
        (files, link) <- phaseCodeGeneratorIridium supplyIridium iridiumCache fullName coreModule options

        sendLog "C" fullName doneModules options
        return (files, link, warnings)
      else do
        iridium <- Iridium.parseModuleIO fullName contents
        return ([Iridium.IridiumFile fullName iridium True], False, 0)

    -- Phase 11: Generate LLVM code
    phaseCodeGeneratorLlvm supplyLlvm (joinPath [filePath, fileName]) iridiumFiles shouldLink options

    putStrLn $ "Compilation successful" ++
                  if warnings == 0 || (NoWarnings `elem` options)
                    then ""
                    else " with " ++ show warnings ++ " warning" ++ if warnings == 1 then "" else "s"

compileHaskellToCore :: String -> String -> String -> [Option] -> Iridium.FileCache -> [String] -> IO (CoreModule, Int)
compileHaskellToCore basedir fullName contents options iridiumCache doneModules = do
  let compileOptions = (options, fullName, doneModules)

  -- Phase 1: Lexing
  (lexerWarnings, tokens) <- 
      doPhaseWithExit 20 (const "L") compileOptions $
          phaseLexer fullName contents options

  unless (NoWarnings `elem` options) $
      showMessages lexerWarnings

  -- Phase 2: Parsing
  parsedModule <- 
    doPhaseWithExit 20 (const "P") compileOptions $
      phaseParser fullName tokens options

  -- Phase 3: Importing
  (indirectionDecls, importEnvsWithMod) <-
      phaseImport fullName parsedModule (resolveDeclarations iridiumCache) options
  let importEnvs = map (\(_,b,_) -> b) importEnvsWithMod

  -- Phase 4: Resolving operators
  resolvedModule <- 
      doPhaseWithExit 20 (const "R") compileOptions $
          phaseResolveOperators parsedModule importEnvs options

  stopCompilingIf (StopAfterParser `elem` options)

  -- Phase 5: Static checking
  (localEnv, typeSignatures, staticWarnings) <-
      doPhaseWithExit 20 (("S"++) . errorsLogCode) compileOptions $
          phaseStaticChecks fullName resolvedModule importEnvsWithMod options        

  unless (NoWarnings `elem` options) $
      showMessages staticWarnings

  stopCompilingIf (StopAfterStaticAnalysis `elem` options)

  -- Phase 6: Kind inferencing (by default turned off)
  let combinedEnv = foldr combineImportEnvironments localEnv importEnvs

  -- print combinedEnv

  when (KindInferencing `elem` options) $
      doPhaseWithExit maximumNumberOfKindErrors (const "K") compileOptions $
        phaseKindInferencer combinedEnv resolvedModule options

  -- Phase 7: Type Inference Directives
  (beforeTypeInferEnv, typingStrategiesDecls) <-
      phaseTypingStrategies fullName combinedEnv typeSignatures options

  -- Phase 8: Type inferencing
  (dictionaryEnv, afterTypeInferEnv, toplevelTypes, allTypeSchemes, solveResult, typeWarnings) <- 
      doPhaseWithExit maximumNumberOfTypeErrors (const "T") compileOptions $ 
          phaseTypeInferencer basedir fullName resolvedModule {-doneModules-} localEnv beforeTypeInferEnv options

  unless (NoWarnings `elem` options) $
      showMessages typeWarnings

  stopCompilingIf (StopAfterTypeInferencing `elem` options)

  -- Phase 9: Desugaring
  coreModule <-
      phaseDesugarer dictionaryEnv
                      fullName resolvedModule allTypeSchemes solveResult
                      (typingStrategiesDecls ++ indirectionDecls) 
                      afterTypeInferEnv
                      toplevelTypes
                      options
  
  let (path, baseName, _) = splitFilePath fullName
  let fullNameNoExt = combinePathAndFile path baseName
  writeFile (fullNameNoExt ++ ".desugared.core") $ show $ pretty coreModule
  verifyCore options "Desugar" coreModule

  stopCompilingIf (StopAfterDesugar `elem` options)

  let number = length staticWarnings + length typeWarnings + length lexerWarnings
  return (coreModule, number)

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (exitWith (ExitFailure 1))

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

maximumNumberOfKindErrors :: Int
maximumNumberOfKindErrors = 1

resolveDeclarations :: Iridium.FileCache -> Id -> IO (Lvm.CoreModule)
resolveDeclarations iridiumCache name = do
  iridium <- Iridium.readIridium iridiumCache name
  return $ toAbstractModule iridium

verifyCore :: [Option] -> String -> Lvm.CoreModule -> IO ()
verifyCore options afterPass mod
  | VerifyBackend `elem` options = Core.checkModuleIO afterPass mod
  | otherwise = return ()
