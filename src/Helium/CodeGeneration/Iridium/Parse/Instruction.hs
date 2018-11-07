module Helium.CodeGeneration.Iridium.Parse.Instruction where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data

pInstruction = do
  pWhitespace
  key <- pKeyword
  case key of
    "let" -> Let <$ pToken '%' <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pExpression <*> pInstruction
    "letalloc" -> LetAlloc <$> pSome pBind pSep <*> pInstruction
      where
        pSep :: Parser Bool
        pSep = do
          pWhitespace
          c <- lookahead
          if c == ',' then do
            pChar
            pWhitespace
            return True
          else
            return False
    "jump" -> Jump <$> pId
    "match" -> Match <$> pVariable <* pWhitespace <* pSymbol "on" <* pWhitespace <*> pDataTypeConstructor <*> pArguments pMatchField <*> pInstruction
    "case" -> Case <$> pVariable <* pWhitespace <*> pCase
    "return" -> Return <$> pVariable
    _ -> pError "expected instruction"

pMatchField :: Parser (Maybe Local)
pMatchField = do
  c <- lookahead
  if c == '_' then do
    pChar
    return Nothing
  else
    Just <$> pLocal

pCase :: Parser Case
pCase = do
  key <- pKeyword
  case key of
    "constructor" -> CaseConstructor <$> pArguments (pCaseAlt pDataTypeConstructor)
    "literal" -> CaseLiteral <$> pArguments (pCaseAlt pLiteral) <* pWhitespace <* pSymbol "otherwise" <* pWhitespace <*> pId
    _ -> pError "expected 'constructor' or 'literal' in case instruction"

pCaseAlt :: Parser a -> Parser (a, BlockName)
pCaseAlt pPattern = (\pat to -> (pat, to)) <$> pPattern <* pWhitespace <* pSymbol "to" <* pWhitespace <*> pId

pBind :: Parser Bind
pBind = Bind <$ pToken '%' <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pBindTarget <* pWhitespace <* pToken '$' <* pWhitespace <*> pArguments pVariable

pBindTarget :: Parser BindTarget
pBindTarget = do
  key <- pKeyword
  case key of
    "thunk" -> BindTargetFunction <$> pVariable
    "constructor" -> BindTargetConstructor <$> pDataTypeConstructor
    _ -> pError "expected bind in letalloc"
