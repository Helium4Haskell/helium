{-| Module      :  PhaseStaticChecks
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Main.PhaseStaticChecks(phaseStaticChecks) where

import Main.CompileUtils
import StaticAnalysis.Messages.Warnings(Warning)
import qualified StaticAnalysis.StaticChecks.StaticChecks as SC
import Syntax.UHA_Syntax (Name)
import Top.Types (TpScheme)
import StaticAnalysis.Messages.StaticErrors
import StaticAnalysis.Messages.Information (showInformation)

phaseStaticChecks :: 
   String -> Module -> [ImportEnvironment] -> [Option] -> 
   Phase Error (ImportEnvironment, [(Name,TpScheme)], [Warning])
phaseStaticChecks fullName module_ importEnvs options = do
    enterNewPhase "Static checking" options

    let (_, baseName, _) = splitFilePath fullName

        res = SC.wrap_Module (SC.sem_Module module_) SC.Inh_Module {
                 SC.baseName_Inh_Module = baseName,
                 SC.importEnvironments_Inh_Module = importEnvs,
                 SC.options_Inh_Module = options }

    case SC.errors_Syn_Module res of
    
       _:_ ->
          do when (DumpInformationForAllModules `elem` options) $
                print (foldr combineImportEnvironments emptyEnvironment importEnvs)
             
             -- display name information
             let combinedEnv = foldr combineImportEnvironments emptyEnvironment importEnvs
             showInformation False options combinedEnv
    
             return (Left $ SC.errors_Syn_Module res)
         
       [] -> 
          return (Right (SC.collectEnvironment_Syn_Module res, SC.typeSignatures_Syn_Module res, SC.warnings_Syn_Module res))