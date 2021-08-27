
{-| Module      :  PhaseStaticChecks
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseDimInferer(phaseDimInferencer) where
import Helium.Main.CompileUtils
import Helium.Utils.Utils (firstUpper)
import Helium.StaticAnalysis.Messages.Warnings(Warning)
import qualified Helium.StaticAnalysis.StaticChecks.StaticChecks as SC
import Helium.Syntax.UHA_Syntax (Name)
import Top.Types (TpScheme)
import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Information (showInformation)
import Helium.Helium.StaticAnalysis.Inference.DimInference.Unification (constraint_solver)
import qualified Helium.Helium.StaticAnalysis.Inference.DimInference.DimInferenceRules as DI

type Location = [String]
data DimError = DimError
                     [Range]                                -- range(s) of the error
                     [MessageLine]                          -- oneliner messages
                     [(Bool, MessageBlock, MessageBlock)]   -- Hugs-like table
                     [DimErrorHint]  

phaseDimInferencer :: 
   String -> String -> Module -> [(Name,ImportEnvironment, ModuleDecls)] -> [Option] -> 
   Phase DimError DimEnvironment -- DimEnvironement built with substitution
phaseDimInferencing basedir fullName module_ importEnvsWithMod options = do
    enterNewPhase "Dimension Inferencing" options

    let dimErrors, substitution = constraint_solver DI.unitConstraints_Syn_Module module_ in
    -- maybe we will rather use a function named dimInferencing if we keep more information

-- take care to the DumpInformation options : what does that do?
    case dimErrors of
    
        _:_ -> Left dimErrors

        [] -> let dimEnvironment = buildDimEnvironment substitution variableToDim in
            Right dimEnvironment

    return dimErrors