module Compile where

import Args(Option(..))
import HeliumMessages(sortAndShowMessages)
import ImportEnvironment
import CoreToImportEnv(getImportEnvironment)
import Strategy(algM, algW)

-- Semantic functions from the ag-world
import qualified PrettyPrinting       (sem_Module)
import qualified ExtractImportDecls   (sem_Module)
import qualified StaticChecks         (sem_Module)
import qualified TypeInferencing      (sem_Module)
import qualified CodeGeneration       (sem_Module)

-- Parser
import Parser(parseModule)
import ParseMessage
import ResolveOperators(resolveOperators, operatorsFromModule)
import OperatorTable
import Lexer

-- UHA
import UHA_Syntax
import UHA_Utils(getNameName, stringFromImportDeclaration, isOperatorName)
import UHA_Range(noRange)

-- LVM
import Standard(getLvmPath, searchPath)
import Id(stringFromId)
import CoreToLvm(coreToLvm)
import CorePretty(corePretty)
import LvmImport(lvmImportDecls)
import qualified Core(CoreDecl)
import CoreRemoveDead( coreRemoveDead ) -- remove dead (import) declarations

-- Logger
import Logger
import Utils(refToCurrentFileName, refToCurrentImported)
import StaticErrors(errorsLogCode)

-- Utilities
import Utils(splitFilePath)
import System(ExitCode(..), exitWith)
import Monad(when, unless)
import IOExts(unsafePerformIO, writeIORef)
import FiniteMap

-- Typing Strategies
import TS_Compile (readTypingStrategiesFromFile)

------------------------------------------------------------------------------------
-- Compiling a single Helium file consists of the following phases:
--   1) Parsing
--   2) Static checking
--   3) Type inferencing
--   4) Desugaring
--   5) Code generation
------------------------------------------------------------------------------------

compile :: String -> [Option] -> [String] -> IO ()
compile fullName options doneModules =
    do
        putStrLn ("Compiling " ++ fullName)

        -- Split file name
        -- e.g. /docs/haskell/Hello.hs =>
        --   filePath = /docs/haskell  baseName = Hello  ext = hs
        --   fullNameNoExt = /docs/haskell/Hello
        let (filePath, baseName, ext) = splitFilePath fullName
            fullNameNoExt = filePath ++ "/" ++ baseName

        -- Phase 1: Parsing
        enterNewPhase "Parsing" options

        when (DumpTokens `elem` options) $ do
            cont <- readFile fullName
            putStrLn (show (layout (lexer (Pos 1 1) cont)))

        parseResult <- {-# SCC "parseModule" #-}
                       parseModule fullName

        mod <- case parseResult of
            Left parseError -> do
                unless (NoLogging `elem` options) $ logger "P" Nothing
                putStr . sortAndShowMessages $ [parseError]
                putStrLn ("Compilation failed with a syntax error")
                exitWith (ExitFailure 1)
            Right m ->
                return m

        -- Add HeliumLang and Prelude import
        let moduleBeforeResolve = addImplicitImports mod

        -- Chase imports
        chasedImpsList <- {-# SCC "chaseImports" #-}
                          chaseImports filePath moduleBeforeResolve

        let indirectionDecls   = concat chasedImpsList
            importEnvironments = {-# SCC "getImportEnvironment" #-}
                                 map (getImportEnvironment baseName) chasedImpsList

        -- Store the current module file-name and its context in
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName
        writeIORef refToCurrentImported doneModules

        let importOperatorTable = operatorsFromModule moduleBeforeResolve
                               ++ concatMap operatorTable importEnvironments
            (module_, resolveErrors) = {-# SCC "resolveOperators" #-}
                      resolveOperators importOperatorTable moduleBeforeResolve

        when (not (null resolveErrors)) $ do
                putStr . sortAndShowMessages $ resolveErrors
                putStrLn ("Compilation failed with a syntax error")
                exitWith (ExitFailure 1)

        when (DumpUHA `elem` options) $
            putStrLn $ show $ PrettyPrinting.sem_Module module_

        stopCompilingIf (StopAfterParser `elem` options)

        -- Phase 2: Static checking
        enterNewPhase "Static checks" options

        let (collectEnvironment, errors, warnings1) =
                {-# SCC "StaticAnalysis" #-}
                StaticChecks.sem_Module module_
                    baseName
                    importEnvironments

        unless (null errors) $
           do
              when (DumpInformationForAllModules `elem` options) $
                 putStrLn (show (foldr combineImportEnvironments emptyEnvironment importEnvironments))
              putStr . sortAndShowMessages $ errors
              unless (NoLogging `elem` options) $ logger ("S"++errorsLogCode errors) Nothing
              let number = length errors
              putStrLn ("Compilation failed with " ++ show number ++ " error" ++ if number == 1 then "" else "s")

        stopCompilingIf (StopAfterStaticAnalysis `elem` options || not (null errors))

        -- Special Phase: Typing Strategies
        let combinedEnvironment = foldr combineImportEnvironments collectEnvironment importEnvironments

        (completeEnvironment, typingStrategiesDecls) <-
           if TypingStrategy `notElem` options
             then
                  return (removeTypingStrategies combinedEnvironment, [])
             else
                  do (typingStrategies, typingStrategiesDecls) <-
                        readTypingStrategiesFromFile
                                         options
                                         (fullNameNoExt ++ ".type")
                                         combinedEnvironment
                     return ( addTypingStrategies typingStrategies combinedEnvironment
                            , typingStrategiesDecls
                            )

        -- Phase 3: Type inferencing
        enterNewPhase "Type inferencing" options

        let (strategy,useTypeGraph)
               | AlgorithmW `elem` options = (algW,False)
               | AlgorithmM `elem` options = (algM,False)
               | otherwise                 = (algW,True ) -- default algorithm W + TypeGraphs

            (debugTypes, toplevelTypes, typeErrors, warnings2) =
                {-# SCC "StaticAnalysis" #-}
                TypeInferencing.sem_Module module_
                    completeEnvironment
                    strategy
                    useTypeGraph

            -- add the top-level types (including the inferred types)
            finalEnvironment = addToTypeEnvironment toplevelTypes completeEnvironment

        when (DumpTypeDebug `elem` options) debugTypes

        unless (null typeErrors) $
           do
              when (DumpInformationForAllModules `elem` options) $
                 putStr (show (foldr combineImportEnvironments emptyEnvironment importEnvironments))
              putStr . ("\n"++) . sortAndShowMessages . take maximumNumberOfTypeErrors . reverse $ typeErrors
              unless (NoLogging `elem` options) $ logger "T" (Just (doneModules,fullName))
              let number = length typeErrors
              when (number > maximumNumberOfTypeErrors) $ putStrLn "(...)\n"
              putStrLn ("Compilation failed with " ++ show number ++ " type error" ++ if number == 1 then "" else "s")

        -- Dump information
        if (DumpInformationForAllModules `elem` options)
          then
             putStrLn (show finalEnvironment)
          else if (DumpInformationForThisModule `elem` options)
                 then
                    putStrLn (show (addToTypeEnvironment toplevelTypes collectEnvironment))
                 else
                    return ()

        stopCompilingIf (StopAfterTypeInferencing `elem` options || not (null typeErrors))

        -- Static Warnings
        let warnings = warnings1 ++ warnings2

        unless (NoWarnings `elem` options) $
            putStr . sortAndShowMessages $ warnings

        -- Phase 4: Desugaring
        enterNewPhase "Desugaring" options

        let moduleWithName = fixModuleName module_ baseName

        let coreModule = {-# SCC "CodeGeneration" #-}
                         CodeGeneration.sem_Module moduleWithName
                            (typingStrategiesDecls ++ indirectionDecls)
                            finalEnvironment
                            toplevelTypes

            strippedCoreModule = coreRemoveDead coreModule

        when (DumpCore `elem` options) $
            print.corePretty $ strippedCoreModule

        when (DumpCoreToFile `elem` options) $ do
            writeFile (fullNameNoExt ++ ".core") $ show.corePretty $ strippedCoreModule
            System.exitWith (ExitSuccess)

        stopCompilingIf (StopAfterDesugar `elem` options)

        -- Phase 5: Code generation
        enterNewPhase "Code generation" options

        catch ( {-# SCC "Daan" #-} coreToLvm fullNameNoExt strippedCoreModule
         ) (\ioError ->
               do
                putStrLn ("Could not write to file '" ++
                            fullNameNoExt ++ ".lvm" ++ "'" ++ show ioError);
                System.exitWith (ExitFailure 1)
           )

        unless (NoLogging `elem` options) $ logger "C" Nothing

        let number = length warnings
        putStrLn $ "Compilation successful" ++
                      if number == 0 || (NoWarnings `elem` options)
                        then ""
                        else " with " ++ show number ++ " warning" ++ if number == 1 then "" else "s"

enterNewPhase :: String -> [Option] -> IO ()
enterNewPhase phase options =
   when (Verbose `elem` options) $
      putStrLn (phase ++ "...")

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (System.exitWith (ExitFailure 1))

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

-- | Make sure the module has a name. If there is no name (module without
--   header) insert the base name of the file name as name.
fixModuleName :: Module -> String -> Module
fixModuleName original@(Module_Module r name es b) baseName =
    case name of
        MaybeName_Nothing ->
            Module_Module r (MaybeName_Just (Name_Identifier noRange [] baseName)) es b
        _ -> original

chaseImports :: String -> Module -> IO [[Core.CoreDecl]]
chaseImports filePath mod =
   do
      lvmPath <- getLvmPath

      let paths           = ".":filePath:lvmPath
          coreImportDecls = ExtractImportDecls.sem_Module mod -- Expand imports
          findModule      = searchPath paths ".lvm" . stringFromId

      lvmImportDecls findModule coreImportDecls

-- Add "import Prelude" if
--   the currently compiled module is not the Prelude and
--   the Prelude is not explicitly imported
-- Always add "import HeliumLang
addImplicitImports :: Module -> Module
addImplicitImports m@(Module_Module moduleRange maybeName exports
                    (Body_Body bodyRange explicitImportDecls decls)) =
    Module_Module
        moduleRange
        maybeName
        exports
        (Body_Body
            bodyRange
            ( case maybeName of
                MaybeName_Just n
                    | getNameName n == "Prelude" -> []
                _ -> if "Prelude" `elem` map stringFromImportDeclaration explicitImportDecls
                     then []
                     else [ implicitImportDecl "Prelude" ]
            ++ [ implicitImportDecl "HeliumLang" ]
            ++ explicitImportDecls
            ) decls
        )
  where

    -- Artificial import declaration for implicit Prelude import
    implicitImportDecl :: String -> ImportDeclaration
    implicitImportDecl moduleName =
        ImportDeclaration_Import
            noRange
            False
            (Name_Identifier noRange [] moduleName)
            MaybeName_Nothing
            MaybeImportSpecification_Nothing
