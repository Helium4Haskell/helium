{-| Module      :  ExpressionTypeInferencer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Infer the type of an expression, and return the type errors that are encountered.
-}

module StaticAnalysis.Inferencers.ExpressionTypeInferencer (expressionTypeInferencer) where

import StaticAnalysis.Inferencers.TypeInferencing (sem_Module, wrap_Module, Inh_Module (..), Syn_Module (..))
import ModuleSystem.ImportEnvironment
import StaticAnalysis.Inferencers.BindingGroupAnalysis (Assumptions)
import StaticAnalysis.Messages.TypeErrors
import Top.Types
import qualified Data.Map as M
import Syntax.UHA_Utils (nameFromString)
import Syntax.UHA_Range (noRange)
import Utils.Utils (internalError)
import Syntax.UHA_Syntax

expressionTypeInferencer :: ImportEnvironment -> Expression -> (TpScheme, Assumptions, TypeErrors)
expressionTypeInferencer importEnvironment expression = 
   let 
       functionName = nameFromString "_"

       module_ = Module_Module noRange MaybeName_Nothing MaybeExports_Nothing body_
       body_   = Body_Body noRange [] [decl_] 
       decl_   = Declaration_PatternBinding noRange pat_ rhs_
       pat_    = Pattern_Variable noRange functionName
       rhs_    = RightHandSide_Expression noRange expression MaybeDeclarations_Nothing

       res = wrap_Module (sem_Module module_) Inh_Module {
       	         importEnvironment_Inh_Module = importEnvironment,
		 options_Inh_Module           = [] }

       inferredType = let err = internalError "ExpressionTypeInferencer.hs" "expressionTypeInferencer" "cannot find inferred type"
                      in maybe err id (M.lookup functionName $ toplevelTypes_Syn_Module res)
                                
   in (inferredType, assumptions_Syn_Module res, typeErrors_Syn_Module res)
