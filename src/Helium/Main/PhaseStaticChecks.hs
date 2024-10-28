{-| Module      :  PhaseStaticChecks
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseStaticChecks(phaseStaticChecks) where
import Helium.ModuleSystem.GatherImports (ModuleDecls)
import Helium.Main.CompileUtils
import Helium.Utils.Utils (firstUpper)
import Helium.StaticAnalysis.Messages.Warnings(Warning)
import qualified Helium.StaticAnalysis.StaticChecks.StaticChecks as SC
import Helium.Syntax.UHA_Syntax (Name)
import Helium.Top.Top.Types (TpScheme)
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Information (showInformation)

phaseStaticChecks :: 
   String -> Module -> [(Name,ImportEnvironment, ModuleDecls)] -> [Option] -> 
   Phase Error (ImportEnvironment, [(Name,TpScheme)], [Warning])
phaseStaticChecks fullName module_ importEnvsWithMod options = do
    enterNewPhase "Static checking" options

    let (_, baseName, _) = splitFilePath fullName
        importEnvs = map (\(_,b,_) -> b) importEnvsWithMod

        res = SC.wrap_Module (SC.sem_Module module_) SC.Inh_Module {
                 SC.baseName_Inh_Module = firstUpper baseName,
                 SC.importEnvironmentsWithMod_Inh_Module = importEnvsWithMod,
                 SC.options_Inh_Module = options }

    case SC.errors_Syn_Module res of
    
       _:_ ->
          do when (DumpInformationForAllModules `elem` options) $
                print (combineImportEnvironmentList importEnvs)
             
             -- display name information
             let combinedEnv = combineImportEnvironmentList importEnvs
             showInformation False options combinedEnv
    
             return (Left $ SC.errors_Syn_Module res)
         
       [] -> 
          return (Right (SC.collectEnvironment_Syn_Module res, SC.typeSignatures_Syn_Module res, SC.warnings_Syn_Module res))