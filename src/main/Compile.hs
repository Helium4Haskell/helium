module Compile where

import Args(Option(..))
import Messages(sortAndShowErrors, sortAndShowTypeErrors,sortAndShowWarnings,Error,TypeError,Warning)
import EnvironmentSynonyms(TypeEnvironment)
import CoreToImportEnv(getImportInfo)
import Strategy(algM, algW)

-- Semantic functions from the ag-world
import qualified PrettyPrinting       (sem_Module)
import qualified ExtractImportDecls   (sem_Module)
import qualified StaticAnalysis       (sem_Module)
import qualified CodeGeneration       (sem_Module)

-- Parser
import Parser(parseModule)
import qualified ResolveOperators(resolveOperators, operatorsFromModule)
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

compile :: String -> [Option] -> [String] -> IO ()
compile fullName options doneModules =
    do
        when (Interpreter `notElem` options) $ putStrLn ("Compiling " ++ fullName)
        -- Split file name
        -- e.g. /docs/haskell/Hello.hs =>
        --   filePath = /docs/haskell  baseName = Hello  ext = hs
        --   fullNameNoExt = /docs/haskell/Hello
        let
            (filePath, baseName, ext) = splitFilePath fullName
            fullNameNoExt = filePath ++ "/" ++ baseName
        
        -- Parser
        when verbose $ putStrLn "Parsing..."
        parseResult <- {-# SCC "parseModule" #-} parseModule fullName
        
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
        chasedImps <- {-# SCC "chaseImports" #-} chaseImports filePath moduleBeforeResolve
        
        let ( importTypeEnv
             ,importConstructorEnv
             ,importTyConEnv
             ,importTypeSynEnv
             ,importOperatorTable
             ,indirectionDecls
             ) =
                    {-# SCC "getImportInfo" #-} getImportInfo baseName chasedImps

        -- Store the current module file-name and its context in 
        -- two IO refs (unsafe! only used for internal error bug-report)
        writeIORef refToCurrentFileName fullName    
        writeIORef refToCurrentImported doneModules
        
        let module_ = {-# SCC "resolveOperators" #-} resolveOperators moduleBeforeResolve importOperatorTable
            
            -- Choose your algorithm for Type Inferencing
            (strategy,useTypeGraph)   
               | AlgorithmW `elem` options = (algW,False)
               | AlgorithmM `elem` options = (algM,False)
               | otherwise                 = (algW,True ) -- default algorithm W + TypeGraphs
            
            -- Tree traversal with the attribute grammar
            (collectedEnv,debugTypes,errors,toplevelTypes, typeErrors , warnings) = 
                {-# SCC "StaticAnalysis" #-}
                StaticAnalysis.sem_Module module_ 
                    baseName 
                    importConstructorEnv  
                    importTyConEnv 
                    importTypeEnv                    
                    importTypeSynEnv 
                    strategy 
                    useTypeGraph

        when (DumpUHA `elem` options) $ 
            putStrLn $ show $ PrettyPrinting.sem_Module module_
        
        when (StopAfterParser `elem` options) $ 
            System.exitWith (ExitFailure 1)
            
        -- Static analysis
        when verbose $ putStrLn "Static analysis..."
        
        (success, finalMessage) <-
            if NoStaticAnalysis `elem` options
            then return (True, "Compilation WITHOUT static analysis 'successful'. Run at your own risk.")
            -- also performs the SA due to lazyness
            else do 
                    -- Optinonally dump type inference information
                    when (null errors && DumpTypeDebug `elem` options) debugTypes                     
                    
                    finalMessage <- showSAMessages
                        options
                        toplevelTypes
                        errors
                        typeErrors
                        warnings
                        debugTypes
                        doneModules
                        fullName
                    return (null errors && null typeErrors, finalMessage)
                
        when (not success || StopAfterStaticAnalysis `elem` options) $ do
            when (Interpreter `notElem` options) $ putStrLn finalMessage
            System.exitWith (ExitFailure 1)
            
        when verbose $ putStrLn "Desugaring..."
        let coreModule = {-# SCC "CodeGeneration" #-}
                            CodeGeneration.sem_Module module_ 
                                collectedEnv 
                                indirectionDecls
                                toplevelTypes
            strippedCoreModule = coreRemoveDead coreModule

        when (DumpCore `elem` options) $ print.corePretty $ strippedCoreModule

        when (DumpCoreToFile `elem` options) $ do
            writeFile (fullNameNoExt ++ ".core") $ show.corePretty $ strippedCoreModule
            System.exitWith (ExitSuccess)

        when (StopAfterDesugar `elem` options) $ 
            System.exitWith (ExitFailure 1)
        
        when verbose $ putStrLn "Code generation..."

        catch ( {-# SCC "Daan" #-} coreToLvm fullNameNoExt strippedCoreModule
         ) (\ioError -> 
               do 
                putStrLn ("Could not write to file '" ++ 
                            fullNameNoExt ++ ".lvm" ++ "'" ++ show ioError);
                System.exitWith (ExitFailure 1)
           )
        
        unless (NoLogging `elem` options) $ logger "C" Nothing
        
        when (Interpreter `notElem` options) $ putStrLn finalMessage
        
    where
        verbose = Verbose `elem` options

chaseImports :: String -> Module -> IO [Core.CoreDecl]
chaseImports filePath mod =
    do
        let coreImportDecls = ExtractImportDecls.sem_Module mod -- Expand imports
            findModule paths id = searchPath paths ".lvm" (stringFromId id)
            
        chasedImps <- lvmImportDecls (findModule (".":filePath:lvmPath)) coreImportDecls
        
        return (concat chasedImps)

-- Expressions 
resolveOperators :: Module -> OperatorTable -> Module
resolveOperators moduleBeforeResolve importOperatorTable =
    let operatorTable = 
            ResolveOperators.operatorsFromModule moduleBeforeResolve
            ++
            importOperatorTable
    in
        ResolveOperators.resolveOperators operatorTable moduleBeforeResolve

maximumNumberOfTypeErrors = 3

showSAMessages :: [Option] -> TypeEnvironment -> [Error] -> [TypeError] -> [Warning] -> IO () -> [String] -> String -> IO String
showSAMessages options toplevelTypes errors typeErrors warnings debugTypes importedSourceFiles fullName 

    | not (null errors) = do
         -- Dump errors
        putStr . unlines . sortAndShowErrors $ errors
        unless (NoLogging `elem` options) $ logger ("S"++errorsLogCode errors) Nothing
        let number = length errors
        return $ "Compilation failed with " ++ show number ++ " error" ++ if number == 1 then "" else "s"
        
    | not (null typeErrors) = do
        -- Dump (first three) type errors 
        putStr . unlines . ("":) . sortAndShowTypeErrors . take maximumNumberOfTypeErrors . reverse $ typeErrors
        unless (NoLogging `elem` options) $ logger "T" (Just (importedSourceFiles,fullName))
        let number = length typeErrors
        when (number > maximumNumberOfTypeErrors) $ putStrLn "(...)\n" 
        return $ "Compilation failed with " ++ show number ++ " type error" ++ if number == 1 then "" else "s"
    
    | otherwise = do
        -- Optionally dump types
        when (DumpTypes `elem` options) $
            putStr . unlines $
                map
                    (\(name,tp) -> show name ++ " :: " ++ show tp)
                    (toList toplevelTypes)                   
                    
        -- Dump warnings
        when (null typeErrors && NoWarnings `notElem` options) $
            putStr . unlines . sortAndShowWarnings $ warnings
        
        let number = length warnings
        return $ "Compilation successful" ++ if number == 0 then "" else
                        " with " ++ show number ++ " warning" ++ if number == 1 then "" else "s"
                         
        
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

lvmPath :: [String]
lvmPath = unsafePerformIO getLvmPath

