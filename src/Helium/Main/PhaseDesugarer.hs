{-| Module      :  PhaseDesugarer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseDesugarer(phaseDesugarer) where

import qualified Data.Map as M
import Helium.Main.CompileUtils
import Text.PrettyPrint.Leijen
import Helium.Top.Top.Solver(SolveResult)
import qualified Helium.Top.Top.Types as Top
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfo (ConstraintInfo)
import Helium.Lvm.Core.Expr(CoreModule, CoreDecl)
import Helium.CodeGeneration.Core.RemoveDead( coreRemoveDead ) -- remove dead (import) declarations
import Helium.CodeGeneration.CoreUtils(TypeInferenceOutput(..))
import Helium.Syntax.UHA_Syntax(Name(..), MaybeName(..))
import Helium.Syntax.UHA_Utils(NameWithRange)
import Helium.Syntax.UHA_Range(noRange)
import Helium.Lvm.Core.Module(moduleDecls, declName, shallowKindFromDecl, declCustoms, accessPublic, declAccess, moduleImports, declModule)
import Helium.ModuleSystem.ImportEnvironment()
import Helium.ModuleSystem.DictionaryEnvironment (DictionaryEnvironment)
import qualified Helium.CodeGeneration.CodeGeneration as CodeGeneration
import Data.List(nubBy, sort, nub)
import Data.Maybe(mapMaybe)
import Helium.Lvm.Common.Id
import Helium.Lvm.Common.IdMap
import Helium.Lvm.Import


phaseDesugarer :: DictionaryEnvironment -> 
                  String -> Module -> M.Map NameWithRange Top.TpScheme -> SolveResult ConstraintInfo -> [CoreDecl] -> 
                    ImportEnvironment ->
                    TypeEnvironment -> [Option] -> IO CoreModule
phaseDesugarer dictionaryEnv fullName module_ fullTypeSchemes solveResult extraDecls afterTypeInferEnv toplevelTypes options = do
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
                    CodeGeneration.toplevelTypes_Inh_Module = toplevelTypes,
                    CodeGeneration.typeOutput_Inh_Module = TypeInferenceOutput solveResult fullTypeSchemes afterTypeInferEnv }

        -- Find imports from the declarations used
        extraModules = nub $ mapMaybe declModule extraDecls
        
        -- Expressions using imported declarations need to be qualified, so we 
        -- create a map from the those declarations
        exported = filter (accessPublic . declAccess) (moduleDecls coreModule)
        (valuesMap, typesMap) = lvmImportRenameMap $ nubDecls (exported ++ extraDecls)

        strippedCoreModule = lvmImportQualifyModule (valuesMap, typesMap) coreModule False

        strippedModuleWithImports = removeDoubleDecls $ coreRemoveDead $ coreModule 
            { moduleDecls = moduleDecls strippedCoreModule
            , moduleImports = extraModules
            }

    when (DumpCore `elem` options) $
        print . pretty $ strippedCoreModule

    when (DumpCoreToFile `elem` options) $ do
        writeFile (fullNameNoExt ++ ".core") $ show . pretty $ strippedModuleWithImports
        exitSuccess
   
    return strippedModuleWithImports

nubDecls :: [CoreDecl] -> [CoreDecl]
nubDecls = nubBy cmp
    where
        cmp x y = shallowKindFromDecl x == shallowKindFromDecl y 
            && declName x == declName y 
            && declModule x == declModule y 

-- It is possible to get double declarations, because we import the same value twice (but has the same origin). We simply remove doubles with same origins and kinds
removeDoubleDecls :: CoreModule -> CoreModule
removeDoubleDecls m =
    let olddecls = moduleDecls m
        newdecls = nubDecls olddecls
    in m {moduleDecls = newdecls}
