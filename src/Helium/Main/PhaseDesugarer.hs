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
import Lvm.Core.Module(moduleDecls, declName, shallowKindFromDecl, declCustoms)
import Lvm.Core.RemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import Helium.ModuleSystem.ImportEnvironment()
import Helium.ModuleSystem.DictionaryEnvironment (DictionaryEnvironment)
import Helium.ModuleSystem.CoreToImportEnv(originFromCustoms)
import qualified Helium.CodeGeneration.CodeGeneration as CodeGeneration
import Data.List(nubBy)


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


        coreModule = CodeGeneration.core_Syn_Module $
            CodeGeneration.wrap_Module (CodeGeneration.sem_Module module_)
                CodeGeneration.Inh_Module {
                    CodeGeneration.dictionaryEnv_Inh_Module = dictionaryEnv,
                    CodeGeneration.extraDecls_Inh_Module    = extraDecls,
                    CodeGeneration.importEnv_Inh_Module     = afterTypeInferEnv,
                    CodeGeneration.toplevelTypes_Inh_Module = toplevelTypes }

        strippedCoreModule = removeDoubleDecls $ coreRemoveDead coreModule

    when (DumpCore `elem` options) $
        print . pretty $ strippedCoreModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core") $ show . pretty $ strippedCoreModule
        exitSuccess
   
    return strippedCoreModule

-- It is possible to get double declarations, because we import the same value twice (but has the same origin). We simply remove doubles with same origins and kinds
removeDoubleDecls :: CoreModule -> CoreModule
removeDoubleDecls m =
    let olddecls = moduleDecls m
        newdecls = nubBy cmp olddecls
        getOrigin = originFromCustoms . declCustoms
        cmp x y = shallowKindFromDecl x == shallowKindFromDecl y && declName x == declName y && getOrigin x == getOrigin y 
    in m {moduleDecls = newdecls}