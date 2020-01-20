module Helium.CodeGeneration.Iridium.Parse.Type where

import Data.Char
import Data.List
import Debug.Trace
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Type
import Lvm.Common.Id
import Lvm.Core.Type

pTypeArgName :: Parser (Either Int String)
pTypeArgName = do
  cs <- pSomeSatisfy "expected type variable" isLower
  c2 <- lookahead
  if cs == "v" && c2 == '$'
    then Left <$ pChar <*> pUnsignedInt
    else return $ Right cs

pTypeArg :: QuantorIndexing -> Parser Int
pTypeArg (QuantorIndexing _ indexNamed indexUnnamed) = do
  arg <- pTypeArgName
  (idx, name) <-
    case arg of
      Left idx -> return (lookup idx indexUnnamed, 'v' : '$' : show idx)
      Right name -> return (lookup name indexNamed, name)
  case idx of
    Just i -> return i
    Nothing -> pError ("Type variable not in scope: " ++ name)

-- Contains the next free id for a type variable, the mapping from names
-- to indices and a mapping from source type variables to new type variables.
-- We maintain the last mapping such that we can more easily assign indices to
-- named type variables.
data QuantorIndexing = QuantorIndexing Int [(String, Int)] [(Int, Int)]

addToMapping :: Eq a => a -> Int -> [(a, Int)] -> [(a, Int)]
addToMapping name idx mapping = (name, idx) : filter ((name /=) . fst) mapping

pQuantor :: QuantorIndexing -> Parser (Quantor, QuantorIndexing)
pQuantor (QuantorIndexing nextIdx stringMapping numberMapping) = do
  var <- pTypeArgName
  case var of
    Left idx ->
      return
        ( Quantor nextIdx Nothing,
          QuantorIndexing (nextIdx + 1) stringMapping (addToMapping idx nextIdx numberMapping)
        )
    Right name ->
      return
        ( Quantor nextIdx (Just name),
          QuantorIndexing (nextIdx + 1) (addToMapping name nextIdx stringMapping) numberMapping
        )

pTypeAtom :: Parser Type
pTypeAtom = pTypeAtom' $ QuantorIndexing 0 [] []

pType :: Parser Type
pType = pType' $ QuantorIndexing 0 [] []

pType' :: QuantorIndexing -> Parser Type
pType' quantors = do
  forallType <- pMaybe $ pTypeForall quantors
  case forallType of
    Just (quantors', tp) -> tp <$> pType' quantors'
    Nothing -> do
      -- Parse function type
      left <- pTypeAp quantors
      arrow <- pMaybe (pSymbol "->")
      case arrow of
        Just _ -> do
          pWhitespace
          right <- pType' quantors
          return $ TAp (TAp (TCon TConFun) left) right
        Nothing -> return left

pTypeAp :: QuantorIndexing -> Parser Type
pTypeAp quantors = do
  tp1 <- pTypeAtom' quantors
  pWhitespace
  tps <- pManyMaybe $ pMaybe (pTypeAtom' quantors <* pWhitespace)
  return $ foldl TAp tp1 tps

pTypeAtom' :: QuantorIndexing -> Parser Type
pTypeAtom' quantors = do
  c1 <- lookahead
  case c1 of
    '!' -> do
      pChar
      pWhitespace
      typeToStrict <$> pTypeAtom' quantors
    '[' -> do
      pChar
      pWhitespace
      c2 <- lookahead
      if c2 == ']'
        then do
          pChar
          return (TCon $ TConDataType $ idFromString "[]")
        else do
          tp <- pType' quantors
          pToken ']'
          return $ TAp (TCon $ TConDataType $ idFromString "[]") tp
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
          return $ TCon $ TConTypeClassDictionary typeClass
        ')' -> do
          pChar
          return $ TCon $ TConTuple 0
        ',' -> do
          commas <- pManySatisfy (== ',')
          pToken ')'
          return $ TCon $ TConTuple $ length commas + 1
        _ -> do
          pWhitespace
          tp <- pType' quantors
          pToken ')'
          return tp
    _ | isLower c1 -> do
      idx <- pTypeArg quantors
      return $ TVar idx
    _ -> TCon . TConDataType <$> pId

pTypeForall :: QuantorIndexing -> Parser (QuantorIndexing, Type -> Type)
pTypeForall quantors = do
  key <- pKeyword
  case key of
    "forall" -> do
      (q, quantors') <- pQuantor quantors
      pWhitespace
      pToken '.'
      pWhitespace
      return (quantors', TForall q KStar)
    _ -> pError "Expected keyword 'forall'"

pFloatPrecision :: Parser FloatPrecision
pFloatPrecision = do
  bits <- pUnsignedInt
  case bits of
    32 -> return Float32
    64 -> return Float64
    _ -> pError $ "Unsupported floating point precision: " ++ show bits

pDataTypeConstructor :: Parser DataTypeConstructor
pDataTypeConstructor =
  DataTypeConstructor
    <$ pToken '@' <*> pId <* pToken ':' <* pWhitespace <*> pTypeAtom

pInstantiation :: QuantorIndexing -> Parser [Type]
pInstantiation quantors = do
  c <- lookahead
  if c == '{'
    then do
      pChar
      pWhitespace
      tp <- pType' quantors
      pToken '}'
      pWhitespace
      tps <- pInstantiation quantors
      return (tp : tps)
    else return []
