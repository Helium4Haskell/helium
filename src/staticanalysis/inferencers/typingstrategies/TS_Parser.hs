module TS_Parser where

import UHA_Syntax
import TS_Syntax
import TS_CoreSyntax
import qualified TS_ToCore
import List (intersperse)
import Data.IORef
import Char
import qualified PrettyPrinting as PP
import qualified ResolveOperators
import Parser
import Parsec
import ParseLibrary hiding (satisfy)
import Lexer
import OperatorTable

parseTypingStrategies :: OperatorTable -> String -> [Token] -> Either ParseError TypingStrategies
parseTypingStrategies operatorTable filename tokens = 
   runHParser (many parseTypingStrategy) filename tokens True {- wait for EOF -}
  
  where

   parseTypingStrategy :: HParser TypingStrategy
   parseTypingStrategy = 
      do lexSIBLINGS
         names <- commas1 (var <|> varop)
         lexSEMI         
         return (TypingStrategy_Siblings names)
      <|>   
      do typerule    <- parseTypeRule 
         constraints <- many parseConstraint
         lexSEMI  
         return (TypingStrategy_TypingStrategy typerule constraints)
      
   parseTypeRule :: HParser TypeRule
   parseTypeRule =         
      do judgements <- many1 parseJudgement
         lexSEMI 
         let (premises, conclusion) = (init judgements, last judgements)
         return (TypeRule_TypeRule (map judgementToSimpleJudgement premises) conclusion)

   parseJudgement :: HParser Judgement
   parseJudgement =         
      do expression <- exp0 
         lexCOLCOL
         exprType   <- type_
         lexSEMI      
         let resolvedExpression = ResolveOperators.expression operatorTable expression
         return (Judgement_Judgement resolvedExpression exprType)     

   parseConstraint :: HParser UserStatement
   parseConstraint = 
      do -- enter a new phase
         lexPHASE
         phase <- fmap read lexInt
         return (UserStatement_Phase (fromInteger phase))
      <|>
      do -- constraint set of meta-variable
         lexCONSTRAINTS         
         name <- varid
         return (UserStatement_MetaVariableConstraints name)
      <|>
      do -- user-constraint
         leftType  <- type_
         lexASGASG
         rightType <- type_
         lexCOL
         msgLines  <- many1 lexString
         let message = concat (intersperse "\n" msgLines)
         return (UserStatement_Constraint leftType rightType message)

judgementToSimpleJudgement :: Judgement -> SimpleJudgement
judgementToSimpleJudgement judgement = 
   case judgement of
      Judgement_Judgement (Expression_Variable _ name) tp 
         -> SimpleJudgement_SimpleJudgement name tp
      Judgement_Judgement expression                   tp 
         -> error ("the following expression should have been a meta-variable: "++showExpression expression)
      
showExpression :: Expression -> String
showExpression = show . PP.sem_Expression
