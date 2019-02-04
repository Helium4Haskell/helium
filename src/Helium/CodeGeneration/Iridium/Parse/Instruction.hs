module Helium.CodeGeneration.Iridium.Parse.Instruction where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id(Id)

pInstruction = do
  pWhitespace
  c <- lookahead
  case c of
    '%' -> Let <$ pChar <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pExpression <*> pInstruction
    _ -> do
      key <- pKeyword
      case key of
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
        "match" -> Match <$> pVariable <* pWhitespace <* pSymbol "on" <* pWhitespace <*> pMatchTarget <* pWhitespace <*> pArguments pMatchField <*> pInstruction
        "case" -> Case <$> pVariable <* pWhitespace <*> pCase
        "return" -> Return <$> pVariable
        "unreachable" -> return Unreachable
        _ -> pError "expected instruction"

pMatchField :: Parser (Maybe Id)
pMatchField = do
  c <- lookahead
  if c == '_' then do
    pChar
    return Nothing
  else
    Just <$ pToken '%' <*> pId

pCase :: Parser Case
pCase = do
  key <- pKeyword
  case key of
    "constructor" -> CaseConstructor <$> pArguments (pCaseAlt pDataTypeConstructor)
    "int" -> CaseInt <$> pArguments (pCaseAlt pUnsignedInt) <* pWhitespace <* pSymbol "otherwise" <* pWhitespace <*> pId
    _ -> pError "expected 'constructor' or 'int' in case instruction"

pCaseAlt :: Parser a -> Parser (a, BlockName)
pCaseAlt pPattern = (\pat to -> (pat, to)) <$> pPattern <* pWhitespace <* pSymbol "to" <* pWhitespace <*> pId

pBind :: Parser Bind
pBind = Bind <$ pToken '%' <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pBindTarget <* pWhitespace <* pToken '$' <* pWhitespace <*> pArguments pVariable

pBindTarget :: Parser BindTarget
pBindTarget = do
  key <- pKeyword
  case key of
    "function" -> BindTargetFunction <$> pVariable
    "thunk" -> BindTargetThunk <$> pVariable
    "constructor" -> BindTargetConstructor <$> pDataTypeConstructor
    "tuple" -> BindTargetTuple <$> pUnsignedInt
    _ -> pError "expected bind in letalloc"

pMatchTarget :: Parser MatchTarget
pMatchTarget = do
  c <- lookahead
  if c == '@' then
    MatchTargetConstructor <$> pDataTypeConstructor
  else do
    key <- pKeyword
    case key of
      "thunk" -> MatchTargetThunk <$> pUnsignedInt
      "tuple" -> MatchTargetTuple <$> pUnsignedInt
      _ -> pError "Expected match target"
