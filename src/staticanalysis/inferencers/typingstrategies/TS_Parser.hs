module TS_Parser where

import UHA_Syntax
import TS_Syntax
import TS_CoreSyntax
import qualified TS_ToCore

import IOExts
import Char

-- Parsing
import qualified ResolveOperators
import Parser
import Parsec
import ParseLibrary
import OperatorTable

{-
--ultimate :: Core_TypingStrategy
ultimate = let ts = head (map TS_ToCore.typingStrategyToCore tmp)
               ts2 :: Core_TypingStrategy
               ts2 = read $ show $ head $ map TS_ToCore.typingStrategyToCore tmp :: Core_TypingStrategy
           in show ts == show ts2 

s = "TypingStrategy (TypeRule [Judgement \"f\" (TVar 0),Judgement \"p\" (TVar 1),Judgement \"q\" (TVar 2)] Judgement \"f <$> p <*> q\" (TVar 3)) [Constraint (TCon \"Int\") (TCon \"Int\") \"???\",MetaVariableConstraints \"f\",Constraint (TVar 0) (TApp (TApp (TCon \"->\") (TVar 4)) (TApp (TApp (TCon \"->\") (TVar 5)) (TVar 6))) \"combi(1)\",Phase 5,Constraint (TVar 1) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 4)) \"combi(2)\",Constraint (TVar 2) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 5)) \"@@ @f.pp@ @p.pp@ @q.pp@ \\n@f.range@ @p.range@ @q.range@ \\n@f.type@ @p.type@ @q.type@ \\n{@t1@} {@t2@} {@t3@} {@t4@} {@s@} {@c@} {@a@} {@b@}\",Constraint (TCon \"Char\") (TCon \"Char\") \"???\",Phase 3,MetaVariableConstraints \"q\",Constraint (TVar 3) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 6)) \"combi(4)\",Constraint (TCon \"Bool\") (TCon \"Bool\") \"???\"]"
s1 = "Judgement \"f\" (TVar 0)"
s2 = "[Constraint (TCon \"Int\") (TCon \"Int\") \"???\",MetaVariableConstraints \"f\",Constraint (TVar 0) (TApp (TApp (TCon \"->\") (TVar 4)) (TApp (TApp (TCon \"->\") (TVar 5)) (TVar 6))) \"combi(1)\",Phase 5,Constraint (TVar 1) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 4)) \"combi(2)\",Constraint (TVar 2) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 5)) \"@@ @f.pp@ @p.pp@ @q.pp@ \\n@f.range@ @p.range@ @q.range@ \\n@f.type@ @p.type@ @q.type@ \\n{@t1@} {@t2@} {@t3@} {@t4@} {@s@} {@c@} {@a@} {@b@}\",Constraint (TCon \"Char\") (TCon \"Char\") \"???\",Phase 3,MetaVariableConstraints \"q\",Constraint (TVar 3) (TApp (TApp (TCon \"Parser\") (TVar 7)) (TVar 6)) \"combi(4)\",Constraint (TCon \"Bool\") (TCon \"Bool\") \"???\"]"
s3 = "(TypeRule [Judgement \"f\" (TVar 0),Judgement \"p\" (TVar 1),Judgement \"q\" (TVar 2)] (Judgement \"f <$> p <*> q\" (TVar 3)))"
tmp = unsafePerformIO 
     (do input <- readFile "Test.type"
         let Right ts = parseTypingStrategies [] "" input 
         return ts)-}

parseTypingStrategies :: OperatorTable -> String -> String -> Either ParseError TypingStrategies
parseTypingStrategies operatorTable filename input = 
   runHParser (many parseTypingStrategy) filename input True {- wait for EOF -} False {- no layout rule -}
  
  where

   parseTypingStrategy :: HParser TypingStrategy
   parseTypingStrategy = 
      do name        <- lexString
         typerule    <- parseTypeRule 
         constraints <- many parseConstraint
         lexSEMI  
         return (TypingStrategy_TypingStrategy name typerule constraints)

   parseTypeRule :: HParser TypeRule
   parseTypeRule =         
      do judgements <- many1 parseJudgement
         lexSEMI 
         let (premises, conclusion) = (init judgements, last judgements)
         return (TypeRule_TypeRule (map judgementToSimpleJudgement premises) conclusion)

   parseJudgement :: HParser Judgement
   parseJudgement =         
      do expression <- exp_ 
         lexSEMI      
         let resolvedExpression = ResolveOperators.expression operatorTable expression
         return (expressionToJudgement resolvedExpression)     

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
         message   <- lexString
         return (UserStatement_Constraint leftType rightType message)

judgementToSimpleJudgement :: Judgement -> SimpleJudgement
judgementToSimpleJudgement judgement = 
   case judgement of
      Judgement_Judgement (Expression_Variable _ name) tp -> SimpleJudgement_SimpleJudgement name tp
      _                                                   -> error "judgementToSimpleJudgement"
      
expressionToJudgement :: Expression -> Judgement
expressionToJudgement expression =
   case expression of
      Expression_Typed _ expression tp -> Judgement_Judgement expression tp
      _                                -> error "expressionToJudgement"
