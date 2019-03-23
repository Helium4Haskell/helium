module Helium.CodeGeneration.Iridium.Parse.Type where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

import Lvm.Common.Id
import Lvm.Core.Type

import Data.List
import Data.Char

pTypeArgName :: Parser (Either Int String)
pTypeArgName = do
  cs <- pSomeSatisfy "expected type variable" isLower
  c2 <- lookahead
  if cs == "v" && c2 == '$' then do
    Left <$> pUnsignedInt
  else
    return $ Right cs

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
addToMapping name idx mapping = (name, idx) : filter ((name /= ) . fst) mapping

pQuantor :: QuantorIndexing -> Parser (Quantor, QuantorIndexing)
pQuantor (QuantorIndexing nextIdx stringMapping numberMapping) = do
  var <- pTypeArgName
  case var of
    Left idx -> return
      ( Quantor nextIdx Nothing
      , QuantorIndexing (nextIdx + 1) stringMapping (addToMapping idx nextIdx numberMapping)
      )
    Right name -> return
      ( Quantor nextIdx (Just name)
      , QuantorIndexing (nextIdx + 1) (addToMapping name nextIdx stringMapping) numberMapping
      )

pCoreType :: Parser Type
pCoreType = pCoreType' $ QuantorIndexing 0 [] []

pCoreType' :: QuantorIndexing -> Parser Type
pCoreType' quantors = do
  forallType <- pMaybe $ pTypeForall quantors
  case forallType of
    Just (quantors', tp) -> tp <$> pCoreType' quantors'
    Nothing -> do
      -- Parse function type
      left <- pCoreTypeAp quantors
      arrow <- pMaybe (pSymbol "->")
      case arrow of
        Just _ -> do
          pWhitespace
          right <- pCoreType' quantors
          return $ TAp (TAp (TCon TConFun) left) right
        Nothing -> return left

pCoreTypeAp :: QuantorIndexing -> Parser Type
pCoreTypeAp quantors = do
  tp1 <- pCoreTypeAtom quantors
  pWhitespace
  tps <- pManyMaybe $ pMaybe (pCoreTypeAtom quantors <* pWhitespace)
  return $ foldl TAp tp1 tps

pCoreTypeAtom :: QuantorIndexing -> Parser Type
pCoreTypeAtom quantors = do
  c1 <- lookahead
  case c1 of
    '[' -> do
      pChar
      pWhitespace
      tp <- pCoreType' quantors
      pToken ']'
      return $ TAp (TCon $ TConDataType $ idFromString "[]") tp
    '(' -> do
      pChar
      c2 <- lookahead
      case c2 of
        ')' -> do
          pChar
          return $ TCon $ TConTuple 0
        ',' -> do
          commas <- pManySatisfy (== ',')
          pToken ')'
          return $ TCon $ TConTuple $ length commas + 1
        _ -> do
          pWhitespace
          tp <- pCoreType' quantors
          pToken ')'
          return tp
    _ | isLower c1 -> do
      idx <- pTypeArg quantors
      return $ TVar idx
    _ -> do
      name <- pId
      return $ TCon $ TConDataType name
  

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

pType :: Parser PrimitiveType
pType = do
  c <- lookahead
  if c == '@' then
    TypeDataType <$ pChar <*> pId
  else do
    key <- pWord
    case key of
      "any" -> return TypeAny
      "any_thunk" -> return TypeAnyThunk
      "any_whnf" -> return TypeAnyWHNF
      "int" -> return TypeInt
      "float" -> TypeFloat <$> pFloatPrecision
      "real_world" -> return TypeRealWorld
      "tuple" -> TypeTuple <$ pWhitespace <*> pUnsignedInt
      "anyfunction" -> return TypeFunction
      "function" -> TypeGlobalFunction <$ pWhitespace <*> pFunctionType
      "unsafeptr" -> return TypeUnsafePtr
      _ -> pError $ "expected type, got " ++ show key ++ " instead"

pFloatPrecision :: Parser FloatPrecision
pFloatPrecision = do
  bits <- pUnsignedInt
  case bits of
    32 -> return Float32
    64 -> return Float64
    _ -> pError $ "Unsupported floating point precision: " ++ show bits

pFunctionType :: Parser FunctionType
pFunctionType = FunctionType <$> pArguments pType <* pWhitespace <* pToken '-' <* pToken '>' <* pWhitespace <*> pType

pDataTypeConstructor :: Parser DataTypeConstructor
pDataTypeConstructor = (\name args dataType -> DataTypeConstructor dataType name args)
  <$ pToken '@' <*> pId <* pToken ':' <* pWhitespace <*> pArguments pType <* pWhitespace <* pSymbol "->" <* pWhitespace <* pToken '@' <*> pId
