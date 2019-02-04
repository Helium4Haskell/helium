module Helium.CodeGeneration.Iridium.Parse.Type where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

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
      _ -> pError "expected type"

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
