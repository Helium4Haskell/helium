{-# LANGUAGE TupleSections #-}

module Helium.CodeGeneration.Iridium.Region.Parse where

import Data.List

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Lvm.Core.Type

import Debug.Trace

data Names = Names
  { quantors :: QuantorNames
  , annotationNames :: [Int]
  , regionNames :: [(Int, Maybe Int)] -- For each lambda depth, the left-most region index
  }

emptyNames :: Names
emptyNames = Names [] [] []

pAnnotation :: Names -> Parser Annotation
pAnnotation names = do
  c1 <- lookahead
  case c1 of
    '∀' -> do
      pChar
      pWhitespace'
      (q, quantors') <- pQuantor (quantors names)
      pWhitespace'
      pToken '.'
      pWhitespace'
      AForall q <$> pAnnotation (names{ quantors = quantors' })
    'λ' -> do
      pChar
      c2 <- lookahead
      case c2 of
        '[' -> do
          pChar
          pToken 'ψ'
          idx <- pSubscriptUnsignedInt
          pWhitespace'
          pToken ':'
          pWhitespace'
          s <- pSortAtom (quantors names)
          pWhitespace'
          pToken ';'
          pWhitespace'
          (names', regionSort) <- pRegionVarsAndSort names
          let names'' = names'{ annotationNames = idx : annotationNames names' }
          pWhitespace'
          pToken ']'
          lc <- pLifetimeContext
          pWhitespace'
          pSymbol "->"
          pWhitespace'
          ALam s regionSort lc <$> pAnnotation names''
        _ -> do
          pToken 'ψ'
          idx <- pSubscriptUnsignedInt
          pWhitespace'
          pToken ':'
          pWhitespace'
          s <- pSortAtom (quantors names)
          pWhitespace'
          pSymbol "->"
          pWhitespace'
          ALam s RegionSortUnit LifetimeContextAny <$> pAnnotation names{ annotationNames = idx : annotationNames names }
    'f' -> do
      keyword <- pKeyword
      case keyword of
        "fix" ->
          (\s -> AFix (identity s) s)
          <$ pToken '{' <* pWhitespace' <*> pSort (quantors names) <* pWhitespace' <* pToken '}'
          <* pWhitespace' <*> pAnnotation names
        "fix_escape" ->
          AFixEscape
          <$ pToken '{' <* pWhitespace' <*> pUnsignedInt <* pWhitespace' <* pToken ';' <* pWhitespace'
          <*> pSort (quantors names) <* pWhitespace' <* pToken ';' <* pWhitespace'
          <*> pRegionSort (quantors names) <* pWhitespace' <* pToken '}' <* pWhitespace'
          <*> pAnnotation names
    _ -> pAnnotationJoin names

pAnnotationJoin :: Names -> Parser Annotation
pAnnotationJoin names = foldr1 AJoin <$> pSome (pAnnotationApp names) pSep
  where
    pSep = do
      pWhitespace'
      c <- lookahead
      case c of
        '⊔' -> True <$ pChar <* pWhitespace'
        _ -> return False

pAnnotationApp :: Names -> Parser Annotation
pAnnotationApp names = foldl apply <$> pAnnotationLeft names <* pWhitespace' <*> pManyMaybe (pArg names <* pWhitespace')
  where
    apply :: Annotation -> Either Type (Annotation, RegionVars, LifetimeContext) -> Annotation
    apply a (Left tp) = AInstantiate a tp
    apply h (Right (AFix f s g, RegionVarsTuple [], LifetimeContextAny))
      | isIdentity f = AFix h s g
    apply a (Right (arg, names, lc)) = AApp a arg names lc

pAnnotationLeft :: Names -> Parser Annotation
pAnnotationLeft names = do
  c <- lookahead
  case c of
    '⊤' -> ATop    <$ pChar <* pWhitespace' <* pToken '{' <* pWhitespace' <*> pSort (quantors names) <* pToken '}'
    '⊥' -> ABottom <$ pChar <* pWhitespace' <* pToken '{' <* pWhitespace' <*> pSort (quantors names) <* pToken '}'
    _ -> pAnnotationPrj names

pArg :: Names -> Parser (Maybe (Either Type (Annotation, RegionVars, LifetimeContext)))
pArg names = do
  c <- lookahead
  case c of
    '[' ->
      (\a r lc -> Just (Right (a, r, lc))) <$ pChar <* pWhitespace' <*> pAnnotation names <* pWhitespace' <* pToken ';' <* pWhitespace' <*> pRegionVars' names <* pWhitespace' <* pToken ']' <*> pLifetimeContext
    '{' -> Just . Left <$ pChar <* pWhitespace' <*> pType' (quantors names) <* pWhitespace' <* pToken '}'
    '(' -> continue
    'T' -> continue
    '⟦' -> continue
    'ψ' -> continue
    _ -> return Nothing
  where
    continue = Just . Right . (, RegionVarsTuple [], LifetimeContextAny) <$> pAnnotationPrj names

pAnnotationPrj :: Names -> Parser Annotation
pAnnotationPrj names = f <$> pAnnotationAtom names <*> pManyMaybe pIndex
  where
    pIndex :: Parser (Maybe Int)
    pIndex = do
      c <- lookahead
      case c of
        '.' -> Just <$ pChar <*> pUnsignedInt
        _ -> return Nothing

    f :: Annotation -> [Int] -> Annotation
    f a xs = foldl AProject a xs

pAnnotationAtom :: Names -> Parser Annotation
pAnnotationAtom names = do
  c <- lookahead
  case c of
    'ψ' -> AVar <$> pAnnotationVar names
    '(' -> tuple <$> pArguments (pAnnotation names)
    'T' -> ATuple <$ pChar <*> pArguments (pAnnotation names)
    '⟦' -> arelation <$> pRelation names
    _ -> pError "Expected annotation"
  where
    tuple [a] = a -- Just a parenthesized annotation
    tuple as = ATuple as

pLifetimeContext :: Parser LifetimeContext
pLifetimeContext = do
  c <- lookahead
  case c of
    '⥜' -> LifetimeContextAny <$ pChar
    _ -> return LifetimeContextLocalBottom

pRelation :: Names -> Parser Relation
pRelation names = relationFromConstraints <$> pArgumentsWith '⟦' '⟧' (pRelationConstraint names)

pRelationConstraint :: Names -> Parser RelationConstraint
pRelationConstraint names = Outlives <$> pRegionVar' names <* pWhitespace' <* pToken '≥' <* pWhitespace' <*> pRegionVar' names

pRegionVar' :: Names -> Parser RegionVar
pRegionVar' names = do
  pToken 'ρ'
  c1 <- lookahead
  case c1 of
    '_' -> do
      pChar
      c2 <- lookahead
      case c2 of
        'g' -> RegionGlobal <$ pSymbol "global"
        'b' -> RegionBottom <$ pSymbol "bottom"
        _ -> pError "Expected global or bottom"
    _ -> do
      idx1 <- pSubscriptInt
      if idx1 < 0 then
        -- Free region variable
        return $ RegionLocal $ length (regionNames names) + 1 - idx1
      else do
        idx2 <- pMaybe (pToken '₋' *> pSubscriptUnsignedInt)
        case (idx1, idx2) `elemIndex` regionNames names of
          Just i -> return $ RegionLocal i
          Nothing -> pError "Region variable not in scope"

pAnnotationVar :: Names -> Parser AnnotationVar
pAnnotationVar names = do
  pToken 'ψ'
  idx <- pSubscriptInt
  if idx < 0 then
    -- Free annotation variable
    return $ AnnotationVar $ length (annotationNames names) + 1 - idx
  else
    case idx `elemIndex` annotationNames names of
      Just i -> return $ AnnotationVar i
      Nothing -> pError "Annotation variable not in scope"

pRegionVars' :: Names -> Parser RegionVars
pRegionVars' names = do
  c <- lookahead
  case c of
    '(' -> RegionVarsTuple <$> pArguments (pRegionVars' names)
    _ -> RegionVarsSingle <$> pRegionVar' names

pSort :: QuantorNames -> Parser Sort
pSort names = do
  c <- lookahead
  case c of
    '∀' -> do
      pChar
      pWhitespace'
      (q, names') <- pQuantor names
      pWhitespace'
      pToken '.'
      pWhitespace'
      SortForall q <$> pSort names'
    '[' -> do
      SortFun
        <$ pChar <* pWhitespace'
        <*> pSort names <* pWhitespace'
        <* pToken ';' <* pWhitespace'
        <*> pRegionSort names <* pWhitespace' <* pToken ']'
        <*> pLifetimeContext <* pWhitespace' <* pSymbol "->" <* pWhitespace'
        <*> pSort names
    _ -> do
      s <- pSortAtom names
      pWhitespace'
      fn <- pMaybe (pSymbol "->")
      case fn of
        Nothing -> return s
        Just _ -> SortFun s RegionSortUnit LifetimeContextAny <$ pWhitespace' <*> pSort names

pSortAtom :: QuantorNames -> Parser Sort
pSortAtom names = do
  c <- pChar
  case c of
    'R' -> return SortRelation
    'Ψ' -> SortPolymorphic <$ pToken '⟨' <* pWhitespace' <*> pTypeArg names <* pWhitespace' <*> pMany (pType' names) pSep <* pToken '⟩'
    'T' -> SortTuple <$> pArguments (pSort names)
    '(' -> tuple <$> pArgumentsWith' ')' (pSort names)
    _ -> pError "Expected sort"
  where
    tuple [s] = s
    tuple sorts = SortTuple sorts

    pSep :: Parser Bool
    pSep = do
      pWhitespace'
      (/= '⟩') <$> lookahead

pRegionSort :: QuantorNames -> Parser RegionSort
pRegionSort names = do
  c1 <- lookahead
  case c1 of
    '(' -> RegionSortTuple <$> pArguments (pRegionSort names)
    '∀' -> do
      pChar
      pWhitespace'
      (q, names') <- pQuantor names
      pWhitespace'
      pToken '.'
      pWhitespace'
      RegionSortForall q <$> pRegionSort names'
    _ -> do
      pToken 'Ρ'
      c2 <- lookahead
      case c2 of
        '⟨' ->
          RegionSortPolymorphic <$ pChar <* pWhitespace' <*> pTypeArg names <* pWhitespace' <*> pMany (pType' names) pSep <* pToken '⟩'
        _ -> return RegionSortMonomorphic
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace'
      (/= '⟩') <$> lookahead

pRegionVarsAndSort :: Names -> Parser (Names, RegionSort)
pRegionVarsAndSort names = do
  c1 <- lookahead
  case c1 of
    '∀' -> do
      pChar
      pWhitespace'
      (q, quantors') <- pQuantor (quantors names)
      pWhitespace'
      pToken '.'
      pWhitespace'
      fmap (RegionSortForall q) <$> pRegionVarsAndSort names{ quantors = quantors' }
    '(' -> do
      pChar
      pWhitespace'
      c2 <- lookahead
      case c2 of
        ')' -> (names, RegionSortTuple []) <$ pChar
        _ -> fmap RegionSortTuple <$> tuple names
    _ -> do
      pToken 'ρ'
      idx1 <- pSubscriptInt
      idx2 <- pMaybe (pToken '₋' *> pSubscriptUnsignedInt)
      let names' = names{ regionNames = (idx1, idx2) : regionNames names }
      pWhitespace'
      pToken ':'
      pWhitespace'
      regionSort <- pRegionSort $ quantors names
      return (names', regionSort)
  where
    tuple :: Names -> Parser (Names, [RegionSort])
    tuple names1 = do
      (names2, regionSort) <- pRegionVarsAndSort names1
      pWhitespace'
      c <- lookahead
      case c of
        ',' ->
          fmap (regionSort : ) <$ pChar <* pWhitespace' <*> tuple names2
        _ -> (names2, [regionSort]) <$ pToken ')' 
