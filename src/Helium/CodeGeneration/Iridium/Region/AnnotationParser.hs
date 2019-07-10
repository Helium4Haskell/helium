module Helium.CodeGeneration.Iridium.Region.AnnotationParser where

import Data.Maybe
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation

pAnnotationVar :: Parser AnnotationVar
pAnnotationVar = pToken 'ψ' *> pIndexVariable

pRegionVar :: Parser RegionVar
pRegionVar = do
  pToken 'ρ'
  c <- lookahead
  if c == '_' then regionGlobal <$ pSymbol "_global" else pIndexVariable

pAnnotation :: Parser Annotation
pAnnotation = do
  c1 <- lookahead
  case c1 of
    'λ' -> do -- Lambda
      pChar
      pToken '['
      argA <- pArgument pSort
      pToken ';'
      pWhitespace
      argR <- pArgument pSortArgumentRegion
      pToken ']'
      pWhitespace
      pSymbol "->"
      pWhitespace
      ALam argA argR <$> pAnnotation
    'f' -> do -- Fix
      pSymbol "fix"
      pWhitespace
      escape <- pMaybe (FixRegionsEscape <$ pSymbol "escape[" <*> pUnsignedInt <* pToken ';' <* pWhitespace <*> pArgument pSortArgumentRegion <* pToken ']')
      let fixRegions = fromMaybe FixRegionsNone escape
      pWhitespace
      pToken ':'
      pWhitespace
      s <- pArgument pSort
      pToken '.'
      AFix fixRegions s <$> pArgument pAnnotation
    '∀' -> do -- Forall
      pChar
      pWhitespace
      AForall <$> pAnnotation
    _ -> pAnnotationJoin

pAnnotationJoin :: Parser Annotation
pAnnotationJoin = do
  a1 <- pAnnotationApp
  c <- lookahead
  if c == '⊔' then AJoin a1 <$ pChar <* pWhitespace <*> pAnnotationJoin else return a1

pAnnotationApp :: Parser Annotation
pAnnotationApp = do
  a1 <- pAnnotationLow
  args <- pManyMaybe pArg
  return $ foldl apply a1 args
  where
    apply a (Left tp) = AInstantiate a tp
    apply a (Right (argA, argR)) = AApp a argA argR

    pArg :: Parser (Maybe (Either Tp (Argument Annotation, Argument RegionVar)))
    pArg = do
      c <- lookahead
      case c of
        '{' -> (Just . Left) <$ pChar <* pWhitespace <*> pTp <* pToken '}' <* pWhitespace
        '[' -> (\a r -> Just $ Right (a, r))
          <$ pChar
          <* pWhitespace
          <*> pArgument pAnnotation
          <* pToken ';'
          <* pWhitespace
          <*> pArgument pRegionVar
          <* pToken ']'
          <* pWhitespace
        _ -> return Nothing

pAnnotationLow :: Parser Annotation
pAnnotationLow = do
  c <- lookahead
  case c of
    '⊥' -> ABottom <$ pChar <* pWhitespace
    'ψ' -> AVar <$> pAnnotationVar <* pWhitespace
    '⟦' -> ARelation <$> pRelationConstraint <* pWhitespace
    't' -> ATuple <$ pSymbol "tuple" <*> pList pAnnotation <* pWhitespace
    'p' -> AProject <$ pSymbol "project(" <*> pAnnotation <* pToken ',' <* pWhitespace <*> pUnsignedInt <* pWhitespace <* pToken ')' <* pWhitespace
    _ -> pToken '⦅' *> pWhitespace *> pAnnotation <* pToken '⦆' <* pWhitespace

pRelationConstraint :: Parser [RelationConstraint]
pRelationConstraint = do
  pToken '⟦'
  constraint <- pConstraint
  constraints <- pManyMaybe pSepConstraint
  pToken '⟧'
  return (constraint : constraints)
  where
    pSepConstraint = do
      c <- lookahead
      if c == ',' then Just <$ pChar <*> pConstraint else return Nothing
    pConstraint = do
      pWhitespace
      r1 <- pRegionVar
      pWhitespace
      pToken '≥'
      pWhitespace
      r2 <- pRegionVar
      pWhitespace
      return $ Outlives r1 r2

-- Parses a parenthesized comma separated list
pList :: Parser a -> Parser [a]
pList = pList'  '(' ')'

pList' :: Char -> Char -> Parser a -> Parser [a]
pList' open close pElem = do
  pToken '('
  pWhitespace
  c <- lookahead
  if c == ')' then [] <$ pChar else pList'
  where
    pList' = do
      pWhitespace
      element <- pElem
      pWhitespace
      c <- lookahead
      case c of
        ',' -> (element :) <$ pChar <* pWhitespace <*> pList'
        _ -> [] <$ pToken ')'

pArgument :: Parser a -> Parser (Argument a)
pArgument pValue = do
  c1 <- lookahead
  if c1 == '(' then do
    ArgumentList <$> pList'  '(' ')' (pArgument pValue) <* pWhitespace
  else do
    ArgumentValue <$> pValue

pSort :: Parser Sort
pSort = do
  c <- lookahead
  case c of
    '∀' -> SortForall <$ pChar <* pWhitespace <*> pSort
    '[' ->
      SortFun
        <$ pChar <* pWhitespace <*> pArgument pSort
        <* pToken ';' <* pWhitespace <*> pArgument pSortArgumentRegion <* pToken ']'
        <* pWhitespace <* pSymbol "->" <* pWhitespace <*> pSort
    'Ψ' -> do
      pChar
      pToken '⟨'
      tvar <- pTypeVar
      tps <- pTpAppInPolymorphicSort
      pToken '⟩'
      return $ SortPolymorphic tvar tps
    _ -> SortRelation <$ pToken 'R' <* pWhitespace

pSortArgumentRegion :: Parser SortArgumentRegion
pSortArgumentRegion = do
  pToken 'Ρ'
  c <- lookahead
  if c == '⟨' then do
    pChar
    tvar <- pTypeVar
    tps <- pTpAppInPolymorphicSort
    pToken '⟩'
    return $ SortArgumentRegionPolymorphic tvar tps
  else
    return SortArgumentRegionMonomorphic

pTpAppInPolymorphicSort :: Parser [Tp]
pTpAppInPolymorphicSort = pWhitespace *> pManyMaybe pTpArg
  where
    pTpArg = do
      c <- lookahead
      if c == '⟩' then return Nothing else Just <$> pTpAtom

pTp :: Parser Tp
pTp = do
  c <- lookahead
  if c == '∀' then do
    pWhitespace
    TpForall <$> pTp
  else do
    arg <- pTpApp
    arrow <- pMaybe (pSymbol "->")
    case arrow of
      Nothing -> return arg
      Just _ -> TpApp (TpApp (TpCon TConFun) arg) <$ pWhitespace <*> pTp

pTpApp :: Parser Tp
pTpApp = do
  t1 <- pTpAtom
  ts <- pManyMaybe (pTpArg)
  return $ foldl TpApp t1 ts
  where
    pTpArg = do
      c <- lookahead
      if c == '}' || c == ')' then return Nothing else Just <$> pTpAtom

pTpAtom :: Parser Tp
pTpAtom = do
  c <- lookahead
  case c of
    '!' -> TpStrict <$ pChar <*> pTpAtom
    '(' -> do
      pChar
      c2 <- lookahead
      case c2 of
        '@' -> do
          pChar
          pSymbol "dictionary"
          pWhitespace
          typeClass <- pId
          pWhitespace
          pToken ')'
          return $ TpCon $ TConTypeClassDictionary typeClass
        ')' -> do
          pChar
          return $ TpCon $ TConTuple 0
        ',' -> do
          commas <- pManySatisfy (== ',')
          pToken ')'
          return $ TpCon $ TConTuple $ length commas + 1
        _ -> do
          pWhitespace
          tp <- pTp
          pToken ')'
          return tp
    _ -> TpVar <$> pTypeVar <* pWhitespace

pTypeVar :: Parser TypeVar
pTypeVar = TypeVar <$ pToken 'α' <*> pSubscript

pIndexVariable :: IndexVariable a => Parser a
pIndexVariable = variableFromIndices <$> pSubscript <* pToken '₋' <*> pSubscript

pSubscript :: Parser Int
pSubscript = do
  sign <- pMaybe (pToken '₋')
  digits <- pManyMaybe (pSubscriptDigit)
  let int = foldl (\a b -> a * 10 + b) 0 digits
  return $ if isJust sign then -int else int

pSubscriptDigit :: Parser (Maybe Int)
pSubscriptDigit = do
  c <- pChar
  return $ case c of
    '₀' -> Just 0
    '₁' -> Just 1
    '₂' -> Just 2
    '₃' -> Just 3
    '₄' -> Just 4
    '₅' -> Just 5
    '₆' -> Just 6
    '₇' -> Just 7
    '₈' -> Just 8
    '₉' -> Just 9
    _ -> Nothing
