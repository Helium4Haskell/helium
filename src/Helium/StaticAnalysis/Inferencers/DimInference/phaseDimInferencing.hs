
{-| Module      :  PhaseStaticChecks
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseDimInferencing(PhaseDimInferencing) where
import Helium.ModuleSystem.GatherImports (ModuleDecls)
import Helium.Main.CompileUtils
import Helium.Utils.Utils (firstUpper)
import Helium.StaticAnalysis.Messages.Warnings(Warning)
import qualified Helium.StaticAnalysis.StaticChecks.StaticChecks as SC
import Helium.Syntax.UHA_Syntax (Name)
import Top.Types (TpScheme)
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Information (showInformation)

phaseDimInferencing :: 
   String -> Module -> [(Name,ImportEnvironment, ModuleDecls)] -> [Option] -> 
   Phase Error (ImportEnvironment, [(Name,TpScheme)], [Warning])
phaseDimInferencing fullName module_ importEnvsWithMod options = do
    enterNewPhase "Dimension Inferencing" options

    {- let (_, baseName, _) = splitFilePath fullName
        importEnvs = map (\(_,b,_) -> b) importEnvsWithMod

        res = SC.wrap_Module (SC.sem_Module module_) SC.Inh_Module {
                 SC.baseName_Inh_Module = firstUpper baseName,
                 SC.importEnvironmentsWithMod_Inh_Module = importEnvsWithMod,
                 SC.options_Inh_Module = options } -}


-- get the units on a good form (normalized) - re-annotation ?
-- Inference rules ?
-- call unification on well-formed unit
-- get the result : Either Fail Substitution

    case {- DimInferencing result -} of
    
        Left Fail -> -- raise an error (we will have to be more and more precise)

        Right substitution -> -- we have made our inferencing