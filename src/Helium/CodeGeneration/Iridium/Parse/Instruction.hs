module Helium.CodeGeneration.Iridium.Parse.Instruction where

import Data.Maybe
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id(Id)
import Lvm.Core.Type

pInstruction :: QuantorIndexing -> Parser Instruction
pInstruction quantors = do
  pWhitespace
  c <- lookahead
  case c of
    '%' -> Let <$ pChar <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pExpression quantors <*> pInstruction quantors
    _ -> do
      key <- pKeyword
      case key of
        "letalloc" -> LetAlloc <$> pSome (pBind quantors) pSep <*> pInstruction quantors
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
        "match" -> Match <$> pVariable quantors <* pWhitespace <* pSymbol "on" <* pWhitespace <*> pMatchTarget <* pWhitespace <*> pInstantiation quantors <*> pArguments pMatchField <*> pInstruction quantors
        "case" -> Case <$> pVariable quantors <* pWhitespace <*> pCase
        "return" -> Return <$> pVariable quantors
        "unreachable" -> Unreachable <$> pMaybe (pVariable quantors)
        "regionrelease" -> RegionRelease <$> pLocal quantors <* pWhitespace <*> pInstruction quantors
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

pBind :: QuantorIndexing -> Parser Bind
pBind quantors = Bind <$ pToken '%'
  <*> pId <* pWhitespace
  <* pToken '=' <* pWhitespace <*> pBindTarget quantors
  <* pWhitespace <* pToken '$' <* pWhitespace
  <*> pCallArguments quantors
  <* pWhitespace
  <*> pAt
  where
    pAt :: Parser RegionVariable
    pAt = fromMaybe RegionGlobal <$> pMaybe (pSymbol "at" *> pRegionVariable quantors)

pRegionVariable :: QuantorIndexing -> Parser RegionVariable
pRegionVariable quantors = do
  c <- lookahead
  if c == '%' then do
    RegionLocal <$> pLocal quantors
  else do
    RegionGlobal <$ pSymbol "global"

pBindTarget :: QuantorIndexing -> Parser BindTarget
pBindTarget quantors = do
  key <- pKeyword
  case key of
    "function" -> BindTargetFunction <$> pGlobalFunction quantors
    "thunk" -> BindTargetThunk <$> pVariable quantors
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
      "tuple" -> MatchTargetTuple <$> pUnsignedInt
      _ -> pError "Expected match target"
