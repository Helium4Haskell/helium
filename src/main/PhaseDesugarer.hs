module PhaseDesugarer(phaseDesugarer) where

import CompileUtils
import CorePretty(corePretty)
import Core(CoreModule, CoreDecl)
import CoreRemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import UHA_Syntax(Module(..), Name(..), MaybeName(..))
import UHA_Range(noRange)
import ImportEnvironment(TypeEnvironment, ImportEnvironment)
import qualified CodeGeneration(sem_Module)

phaseDesugarer :: String -> Module -> [CoreDecl] -> 
                    ImportEnvironment -> TypeEnvironment -> [Option] -> IO CoreModule
phaseDesugarer fullName module_ extraDecls finalEnv toplevelTypes options = do
    enterNewPhase "Desugaring" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName

        moduleWithName = fixModuleName module_ baseName

        coreModule = 
            CodeGeneration.sem_Module moduleWithName
                extraDecls
                finalEnv
                toplevelTypes

        strippedCoreModule = coreRemoveDead coreModule

    when (DumpCore `elem` options) $
        print.corePretty $ strippedCoreModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core") $ show.corePretty $ strippedCoreModule
        exitWith (ExitSuccess)
   
    return strippedCoreModule

-- | Make sure the module has a name. If there is no name (module without
--   header) insert the base name of the file name as name.
fixModuleName :: Module -> String -> Module
fixModuleName original@(Module_Module r name es b) baseName =
    case name of
        MaybeName_Nothing ->
            Module_Module r (MaybeName_Just (Name_Identifier noRange [] baseName)) es b
        _ -> original


