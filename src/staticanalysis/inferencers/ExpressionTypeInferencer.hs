module ExpressionTypeInferencer (expressionTypeInferencer) where

import TypeInferencing (sem_Module)
import ImportEnvironment
import Strategy (algW)
import TypeErrors
import Types
import FiniteMap
import UHA_Utils (noRange, nameFromString)
import Utils (internalError)
import UHA_Syntax

expressionTypeInferencer :: ImportEnvironment -> Expression -> (TpScheme, TypeErrors)
expressionTypeInferencer importEnvironment expression = 
   let 
       functionName = nameFromString "_"

       module_  = Module_Module 
                     noRange
                     MaybeName_Nothing 
                     MaybeExports_Nothing
                     (Body_Body
                         noRange
                         []
                         [ Declaration_PatternBinding
                              noRange
                              (Pattern_Variable
                                  noRange
                                  functionName)
                              (RightHandSide_Expression 
                                  noRange 
                                  expression
                                  MaybeDeclarations_Nothing)])
                         
       (_, typeEnvironment, errors, _) 
                = sem_Module 
                     module_
                     importEnvironment
                     algW                   
                     False
                     
       inferredType = let err = internalError "ExpressionTypeInferencer.hs" "expressionTypeInferencer" "cannot find inferred type"
                      in maybe err id (lookupFM typeEnvironment functionName)
                                
   in (inferredType, errors)
