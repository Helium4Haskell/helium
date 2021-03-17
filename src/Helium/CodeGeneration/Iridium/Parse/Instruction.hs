module Helium.CodeGeneration.Iridium.Parse.Instruction where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id(Id)
import Lvm.Core.Type

pInstruction :: QuantorNames -> Parser Instruction
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
        "newregion" -> NewRegion <$> pRegionVar <* pWhitespace <*> pRegionSize <* pWhitespace <*> pInstruction quantors
        "release" -> ReleaseRegion <$> pRegionVar <* pWhitespace <*> pInstruction quantors
        "jump" -> Jump <$> pId
        "match" -> Match <$> pLocal quantors <* pWhitespace <* pSymbol "on" <* pWhitespace <*> pMatchTarget <* pWhitespace <*> pInstantiation quantors <*> pArguments pMatchField <*> pInstruction quantors
        "case" -> Case <$> pLocal quantors <* pWhitespace <*> pCase
        "return" -> Return <$> pLocal quantors
        "unreachable" -> Unreachable <$> pMaybe (pLocal quantors)
        _ -> pError "expected instruction"

pRegionSize :: Parser (Maybe Int)
pRegionSize = do
  key <- pKeyword
  case key of
    "bounded" -> Just <$> pUnsignedInt
    "unbounded" -> return Nothing
    _ -> pError "expected region size"

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

pBind :: QuantorNames -> Parser Bind
pBind quantors = Bind <$ pToken '%' <*> pId <* pWhitespace <* pToken '=' <* pWhitespace <*> pBindTarget quantors <* pWhitespace <* pToken '$' <* pWhitespace <*> pCallArguments quantors <* pWhitespace <*> pAtRegion

pBindTarget :: QuantorNames -> Parser BindTarget
pBindTarget quantors = do
  key <- pKeyword
  case key of
    "function" -> uncurry . BindTargetFunction <$> pGlobalFunction <* pWhitespace <*> pFunctionRegions
    "thunk" -> BindTargetThunk <$> pVariable quantors <* pWhitespace <*> pThunkRegions
    "constructor" -> BindTargetConstructor <$> pDataTypeConstructor
    "tuple" -> BindTargetTuple <$> pUnsignedInt
    _ -> pError "expected bind in letalloc"
  where
    pFunctionRegions :: Parser (RegionVars, BindThunkRegions)
    pFunctionRegions
      = pTry (RegionVarsTuple [], BindThunkRegions (RegionVarsTuple []) (RegionVarsTuple []))
        ((\r1 r2 r3 -> (r1, BindThunkRegions r2 r3))
          <$ pToken '$' <* pWhitespace <* pToken '(' <* pWhitespace
          <*> pRegionVars
          <* pWhitespace <* pToken ',' <* pWhitespace
          <*> pRegionVars
          <* pWhitespace <* pToken ',' <* pWhitespace
          <*> pRegionVars
          <* pWhitespace <* pToken ')' <* pWhitespace
        )

    pThunkRegions :: Parser BindThunkRegions
    pThunkRegions
      = pTry (BindThunkRegions (RegionVarsTuple []) (RegionVarsTuple []))
        (BindThunkRegions
          <$ pToken '$' <* pWhitespace <* pToken '(' <* pWhitespace
          <*> pRegionVars
          <* pWhitespace <* pToken ',' <* pWhitespace
          <*> pRegionVars
          <* pWhitespace <* pToken ')' <* pWhitespace
        )

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
