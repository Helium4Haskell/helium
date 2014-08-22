{-| Module      :  PhaseDesugarer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseDesugarer(phaseDesugarer) where

import Helium.Main.CompileUtils
import Text.PrettyPrint.Leijen
import Lvm.Core.Expr(CoreModule, CoreDecl)
import Lvm.Core.RemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import Helium.Syntax.UHA_Syntax(Name(..), MaybeName(..))
import Helium.Syntax.UHA_Range(noRange)
import Helium.ModuleSystem.ImportEnvironment()
import Helium.ModuleSystem.DictionaryEnvironment (DictionaryEnvironment)
import qualified Helium.CodeGeneration.CodeGeneration as CodeGeneration

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

        coreModule = CodeGeneration.core_Syn_Module $
            CodeGeneration.wrap_Module (CodeGeneration.sem_Module moduleWithName)
                CodeGeneration.Inh_Module {
                    CodeGeneration.dictionaryEnv_Inh_Module = dictionaryEnv,
                    CodeGeneration.extraDecls_Inh_Module    = extraDecls,
                    CodeGeneration.importEnv_Inh_Module     = afterTypeInferEnv,
                    CodeGeneration.toplevelTypes_Inh_Module = toplevelTypes }

        strippedCoreModule = coreRemoveDead coreModule

    when (DumpCore `elem` options) $
        print . pretty $ strippedCoreModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core") $ show . pretty $ strippedCoreModule
        exitSuccess
   
    return strippedCoreModule

-- | Make sure the module has a name. If there is no name (module without
--   header) insert the base name of the file name as name.
fixModuleName :: Module -> String -> Module
fixModuleName original@(Module_Module r name es b) baseName =
    case name of
        MaybeName_Nothing ->
            Module_Module r (MaybeName_Just (Name_Identifier noRange [] baseName)) es b -- !!!Name
        _ -> original


