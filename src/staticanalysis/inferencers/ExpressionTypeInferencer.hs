{-| Module      :  ExpressionTypeInferencer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Infer the type of an expression, and return the type errors that are encountered.
-}

module ExpressionTypeInferencer (expressionTypeInferencer) where

import TypeInferencing (sem_Module)
import ImportEnvironment
import TypeErrors
import Top.Types
import Data.FiniteMap
import UHA_Utils (nameFromString)
import UHA_Range (noRange)
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
                         
       (_, _, _, typeEnvironment, errors, _) 
                = sem_Module 
                     module_
                     importEnvironment                                        
                     []
                     
       inferredType = let err = internalError "ExpressionTypeInferencer.hs" "expressionTypeInferencer" "cannot find inferred type"
                      in maybe err id (lookupFM typeEnvironment functionName)
                                
   in (inferredType, errors)
