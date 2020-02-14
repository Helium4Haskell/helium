module Helium.CodeGeneration.Iridium.Parse.Instruction
  ( pInstruction,
  )
where

import Control.Applicative
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Lvm.Common.Id (Id)
import qualified Text.Parsec as P

pInstruction :: Parser Instruction
pInstruction = pLet <|> pLetAlloc <|> pJump <|> pMatch <|> pCase <|> pReturn <|> pUnreachable

pLet :: Parser Instruction
pLet = Let <$ pToken '%' <*> pId <* pToken '=' <*> pExpression <*> pInstruction

pLetAlloc :: Parser Instruction
pLetAlloc = LetAlloc <$ pSymbol "letalloc" <*> P.sepBy pBind (pToken ',') <*> pInstruction

pJump :: Parser Instruction
pJump = Jump <$ pSymbol "jump" <*> pId

pMatch :: Parser Instruction
pMatch = Match <$ pSymbol "match" <*> pVariable <* pSymbol "on" <*> pMatchTarget <*> pInstantiation <*> pArguments pMatchField <*> pInstruction

pCase :: Parser Instruction
pCase = Case <$ pSymbol "case" <*> pVariable <*> (pCaseConstructor <|> pCaseInt)

pReturn :: Parser Instruction
pReturn = Return <$ pSymbol "return" <*> pVariable

pUnreachable :: Parser Instruction
pUnreachable = Unreachable <$ pSymbol "unreachable" <*> P.optionMaybe (pVariable)

pMatchField :: Parser (Maybe Id)
pMatchField = Nothing <$ pToken '_' <|> Just <$ pToken '%' <*> pId

pCaseConstructor :: Parser Case
pCaseConstructor = CaseConstructor <$ pSymbol "constructor" <*> pArguments (pCaseAlt pDataTypeConstructor)

pCaseInt :: Parser Case
pCaseInt = CaseInt <$ pSymbol "int" <*> pArguments (pCaseAlt pUnsignedInt) <* pSymbol "otherwise" <*> pId

pCaseAlt :: Parser a -> Parser (a, BlockName)
pCaseAlt pPattern = (\pat to -> (pat, to)) <$> pPattern <* pSymbol "to" <*> pId

pBind :: Parser Bind
pBind = Bind <$ pToken '%' <*> pId <* pToken '=' <*> pBindTarget <* pToken '$' <*> pCallArguments

pBindTarget :: Parser BindTarget
pBindTarget = pBindTargetFunction <|> pBindTargetThunk <|> pBindTargetConstructor <|> pBindTargetTuple

pBindTargetFunction :: Parser BindTarget
pBindTargetFunction = BindTargetFunction <$ pSymbol "function" <*> pGlobalFunction

pBindTargetThunk :: Parser BindTarget
pBindTargetThunk = BindTargetThunk <$ P.try (pSymbol "thunk") <*> pVariable

pBindTargetConstructor :: Parser BindTarget
pBindTargetConstructor = BindTargetConstructor <$ pSymbol "constructor" <*> pDataTypeConstructor <*> P.optionMaybe pReuse

pReuse :: Parser Id
pReuse = pSymbol "reuse" *> pToken '%' *> pId

pBindTargetTuple :: Parser BindTarget
pBindTargetTuple = BindTargetTuple <$ pSymbol "tuple" <*> pUnsignedInt <*> P.optionMaybe pReuse

pMatchTarget :: Parser MatchTarget
pMatchTarget = pMatchTargetConstructor <|> pMatchTargetTuple

pMatchTargetConstructor :: Parser MatchTarget
pMatchTargetConstructor = MatchTargetConstructor <$> pDataTypeConstructor

pMatchTargetTuple :: Parser MatchTarget
pMatchTargetTuple = MatchTargetTuple <$ pSymbol "tuple" <*> pUnsignedInt
