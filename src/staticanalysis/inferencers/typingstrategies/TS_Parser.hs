module TS_Parser where

import UHA_Syntax
import TS_Syntax
import Parsec
import ParseCommon
import HaskellLexer hiding (conid, varid)
import ParseType
import ParseDeclExp
import OperatorTable
import Char
import qualified ResolveOperators

parseTypingStrategies :: OperatorTable -> String -> String -> Either ParseError TypingStrategies
parseTypingStrategies operatorTable filename input = 
   runHParser (many parseTypingStrategy) filename input 
  
  where

   parseTypingStrategy :: HParser TypingStrategy
   parseTypingStrategy = 
      do name        <- stringLiteral
         typerule    <- parseTypeRule 
         constraints <- many parseConstraint
         reservedOp ";"  
         return (TypingStrategy_TypingStrategy name typerule constraints)

   parseTypeRule :: HParser TypeRule
   parseTypeRule =         
      do premises   <- commas parseSimpleJudgement
         reservedOp ";"
         conclusion <- parseJudgement
         reservedOp ";"      
         return (TypeRule_TypeRule premises conclusion)

   parseJudgement :: HParser Judgement
   parseJudgement =         
      do expression <- exp_ 
         reservedOp ";"
         uhaType    <- type_
         let resolvedExpression = ResolveOperators.expression operatorTable expression
         return (Judgement_Judgement resolvedExpression uhaType)

   parseSimpleJudgement :: HParser SimpleJudgement
   parseSimpleJudgement =         
      do name    <- varid
         reservedOp ";"
         uhaType <- type_
         return (SimpleJudgement_SimpleJudgement name uhaType)      

   parseConstraint :: HParser UserStatement
   parseConstraint = 
      do -- enter a new phase
         reserved "phase"
         phase <- natural
         return (UserStatement_Phase (fromInteger phase))
      <|>
      do -- constraint set of meta-variable
         reserved "constraints"         
         name <- varid
         return (UserStatement_MetaVariableConstraints name)
      <|>
      do -- user-constraint
         leftType  <- type_
         reservedOp "=="
         rightType <- type_
         reservedOp ":"
         message   <- stringLiteral
         return (UserStatement_Constraint leftType rightType message)
