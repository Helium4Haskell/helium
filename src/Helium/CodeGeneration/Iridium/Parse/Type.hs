module Helium.CodeGeneration.Iridium.Parse.Type where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

import Helium.Lvm.Common.Id
import Helium.Lvm.Core.Type

import Data.List
import Data.Char

pTypeArgName :: Parser (Either Int String)
pTypeArgName = do
  cs <- pSomeSatisfy "expected type variable" isLower
  c2 <- lookahead
  if cs == "v" && c2 == '$' then do
    Left <$ pChar <*> pUnsignedInt
  else
    return $ Right cs

pTypeArg :: QuantorNames -> Parser Int
pTypeArg quantorNames = do
  arg <- pTypeArgName
  case arg of
    Left idx
      | idx >= length quantorNames -> pError $ "Unnamed type argument v$" ++ show idx ++ " not in scope"
      | otherwise -> return idx
    Right name -> case name `elemIndex` quantorNames of
      Nothing -> pError $ "Type argument " ++ show name ++ " not in scope"
      Just idx -> return idx

pQuantor :: QuantorNames -> Parser (Quantor, QuantorNames)
pQuantor quantorNames = do
  var <- pTypeArgName
  case var of
    Left idx
      | idx /= length quantorNames -> pError $ "Identifier for type argument v$" ++ show idx ++ " doesn't match the next fresh type argument v$" ++ show (length quantorNames)
      | otherwise -> return (Quantor Nothing, ("v$" ++ show idx) : quantorNames)
    Right name -> return
      ( Quantor (Just name)
      , name : quantorNames
      )

pTypeAtom :: Parser Type
pTypeAtom = pTypeAtom' []

pType :: Parser Type
pType = pType' []

pType' :: QuantorNames -> Parser Type
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

pTypeAp :: QuantorNames -> Parser Type
pTypeAp quantors = do
  tp1 <- pTypeAtom' quantors
  pWhitespace
  tps <- pManyMaybe $ pMaybe (pTypeAtom' quantors <* pWhitespace)
  return $ foldl TAp tp1 tps

pTypeAtom' :: QuantorNames -> Parser Type
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
      if c2 == ']' then do
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
    _ -> do
      name <- pId
      return $ TCon $ TConDataType name

pTypeForall :: QuantorNames -> Parser (QuantorNames, Type -> Type)
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
pDataTypeConstructor = DataTypeConstructor
  <$ pToken '@' <*> pId <* pToken ':' <* pWhitespace <*> pTypeAtom

pInstantiation :: QuantorNames -> Parser [Type]
pInstantiation quantors = do
  c <- lookahead
  if c == '{' then do
    pChar
    pWhitespace
    tp <- pType' quantors
    pToken '}'
    pWhitespace
    tps <- pInstantiation quantors
    return (tp : tps)
  else return []
