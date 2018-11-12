module Helium.CodeGeneration.Iridium.Parse.Type where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

pType :: Parser PrimitiveType
pType = do
  key <- pWord
  case key of
    "any" -> return TypeAny
    "any_thunk" -> return TypeAnyThunk
    "any_whnf" -> return TypeAnyWHNF
    "int" -> return TypeInt
    "anyfunction" -> return TypeFunction
    "function" -> TypeGlobalFunction <$> pFunctionType
    "data" -> TypeDataType <$ pWhitespace <* pToken '@' <*> pId
    "unsafeptr" -> return TypeUnsafePtr
    _ -> pError "expected type"

pFunctionType :: Parser FunctionType
pFunctionType = FunctionType <$> pArguments pType <* pWhitespace <* pToken '-' <* pToken '>' <* pWhitespace <*> pType

pDataTypeConstructor :: Parser DataTypeConstructor
pDataTypeConstructor = (\name args dataType -> DataTypeConstructor dataType name args)
  <$ pToken '@' <*> pId <* pToken ':' <* pWhitespace <*> pArguments pType <* pWhitespace <* pSymbol "->" <* pWhitespace <* pToken '@' <*> pId
