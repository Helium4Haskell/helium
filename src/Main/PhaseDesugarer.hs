{-| Module      :  PhaseDesugarer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Main.PhaseDesugarer(phaseDesugarer) where

import Main.CompileUtils
import Text.PrettyPrint.Leijen
import Lvm.Core.Expr(CoreModule, CoreDecl)
import Lvm.Core.RemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import Syntax.UHA_Syntax(Name(..), MaybeName(..))
import Syntax.UHA_Range(noRange)
import ModuleSystem.ImportEnvironment()
import ModuleSystem.DictionaryEnvironment (DictionaryEnvironment)
import qualified CodeGeneration.CodeGeneration as CodeGeneration

phaseDesugarer :: DictionaryEnvironment -> 
                  String -> Module -> [CoreDecl] -> 
                    ImportEnvironment ->
                    TypeEnvironment -> [Option] -> IO CoreModule
phaseDesugarer dictionaryEnv fullName module_ extraDecls afterTypeInferEnv toplevelTypes options = do
    enterNewPhase "Desugaring" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName

{- hier kunnen we misschien main inserten en dan is toplevelTypes niet nodig in AG. 

en eigenlijk is afterTypeInferEnv te groot. alleen locale types en constructoren hoeven gezien te worden

-}

        moduleWithName = fixModuleName module_ baseName

        coreModule = fst $
            CodeGeneration.sem_Module moduleWithName                
                dictionaryEnv
                extraDecls
                afterTypeInferEnv
                toplevelTypes            

        strippedCoreModule = coreRemoveDead coreModule

    when (DumpCore `elem` options) $
        print . pretty $ strippedCoreModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core") $ show . pretty $ strippedCoreModule
        exitWith (ExitSuccess)
   
    return strippedCoreModule

-- | Make sure the module has a name. If there is no name (module without
--   header) insert the base name of the file name as name.
fixModuleName :: Module -> String -> Module
fixModuleName original@(Module_Module r name es b) baseName =
    case name of
        MaybeName_Nothing ->
            Module_Module r (MaybeName_Just (Name_Identifier noRange [] baseName)) es b -- !!!Name
        _ -> original


