module Compile where

import Args(Option(..))
import Messages(sortAndShow,Error,TypeError,Warning)
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
import ResolveOperators(resolveOperators, operatorsFromModule)
import OperatorTable

-- UHA
import UHA_Syntax
import UHA_Utils(noRange, getNameName, stringFromImportDeclaration)

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
import Messages(errorsLogCode)

-- Utilities
import SortedAssocList(toList)
import Utils(splitFilePath)
import System(ExitCode(..), exitWith)
import Monad(when, unless)
import IOExts(unsafePerformIO, writeIORef)

-- Temporary !!!!!
import SortedAssocList
import FiniteMap
import Types (TpScheme)

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
        when (Interpreter `notElem` options) $ 
           putStrLn ("Compiling " ++ fullName)
           
        -- Split file name
        -- e.g. /docs/haskell/Hello.hs =>
        --   filePath = /docs/haskell  baseName = Hello  ext = hs
        --   fullNameNoExt = /docs/haskell/Hello
        let (filePath, baseName, ext) = splitFilePath fullName
            fullNameNoExt = filePath ++ "/" ++ baseName
         
        -- Phase 1: Parsing
        enterNewPhase "Parsing" options
        
        parseResult <- {-# SCC "parseModule" #-} 
                       parseModule fullName
        
        mod <- case parseResult of
            Left errorString -> do
                unless (NoLogging `elem` options) $ logger "P" Nothing
                putStrLn errorString
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
            module_ = {-# SCC "resolveOperators" #-} 
                      resolveOperators importOperatorTable moduleBeforeResolve

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
              putStr . unlines . sortAndShow $ errors
              unless (NoLogging `elem` options) $ logger ("S"++errorsLogCode errors) Nothing
              let number = length errors
              when (Interpreter `notElem` options) $ 
                 putStrLn ("Compilation failed with " ++ show number ++ " error" ++ if number == 1 then "" else "s")

        stopCompilingIf (StopAfterStaticAnalysis `elem` options || not (null errors)) 
      
        -- Phase 3: Type inferencing
        enterNewPhase "Type inferencing" options
        
        let (strategy,useTypeGraph)   
               | AlgorithmW `elem` options = (algW,False)
               | AlgorithmM `elem` options = (algM,False)
               | otherwise                 = (algW,True ) -- default algorithm W + TypeGraphs
                                    
            completeEnvironment = foldr combineImportEnvironments collectEnvironment importEnvironments
                     
            (debugTypes, toplevelTypes, typeErrors, warnings2) = 
                {-# SCC "StaticAnalysis" #-} 
                TypeInferencing.sem_Module module_ 
                    completeEnvironment
                    strategy 
                    useTypeGraph
        
            finalEnvironment = foldr (uncurry addType) completeEnvironment (toList toplevelTypes)    

        unless (null typeErrors) $
           do 
              putStr . unlines . ("":) . sortAndShow . take maximumNumberOfTypeErrors . reverse $ typeErrors
              unless (NoLogging `elem` options) $ logger "T" (Just (doneModules,fullName))
              let number = length typeErrors
              when (number > maximumNumberOfTypeErrors) $ putStrLn "(...)\n" 
              when (Interpreter `notElem` options) $ 
                 putStrLn ("Compilation failed with " ++ show number ++ " type error" ++ if number == 1 then "" else "s")

        -- Dump inferred top-level types
        when (DumpTypes `elem` options) $
            putStr . unlines $
                map
                    (\(name,tp) -> show name ++ " :: " ++ show tp)
                    (toList toplevelTypes)                   

        stopCompilingIf (StopAfterTypeInferencing `elem` options || not (null typeErrors))         
                    
        -- Static Warnings        
        let warnings = warnings1 ++ warnings2
            
        unless (NoWarnings `elem` options) $
            putStr . unlines . sortAndShow $ warnings
                           
        -- Phase 4: Desugaring
        enterNewPhase "Desugaring" options
        
        let coreModule = {-# SCC "CodeGeneration" #-}
                         CodeGeneration.sem_Module module_ 
                             (valueConstructors finalEnvironment)
                             indirectionDecls
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
        when (Interpreter `notElem` options) $ 
           putStrLn $ "Compilation successful" ++ 
                      if number == 0 || (NoWarnings `elem` options)   
                        then "" 
                        else " with " ++ show number ++ " warning" ++ if number == 1 then "" else "s"          

enterNewPhase :: String -> [Option] -> IO ()
enterNewPhase phase options = 
   when (Interpreter `notElem` options && Verbose `elem` options) $
      putStrLn (phase ++ "...")

stopCompilingIf :: Bool -> IO ()
stopCompilingIf bool = when bool (System.exitWith (ExitFailure 1))

maximumNumberOfTypeErrors :: Int
maximumNumberOfTypeErrors = 3

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
