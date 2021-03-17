module Helium.CodeGeneration.Iridium.Parse.Method where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import qualified Helium.CodeGeneration.Iridium.Region.Parse as Region
import Lvm.Common.Id(Id, idFromString)
import Lvm.Core.Type
import Data.Maybe

pMethod :: Parser Method
pMethod = do
  c <- lookahead
  tp <- if c == ':' then do
    pToken ':'
    pWhitespace
    pToken '{'
    pWhitespace
    tp <- pType
    pWhitespace
    pToken '}'
    pWhitespace
    pToken '$'
    pWhitespace
    return $ Just tp
  else
    return Nothing
  additionalRegions <- pTry (RegionVarsTuple []) (pRegionVars <* pWhitespace)
  pToken '('
  pWhitespace
  c <- lookahead
  (args, quantors) <-
    if c == ')' then
      return ([], [])
    else
      pMethodArguments []
  pToken ')'
  pWhitespace
  pToken ':'
  pWhitespace
  returnType <- pType' quantors
  returnRegions <- pAtRegions
  pWhitespace
  annotations <- pAnnotations
  c <- pChar
  let tp' = fromMaybe (typeFromFunctionType $ FunctionType (map toArg args) returnType) tp
  case c of
    '{' ->
      (\(b:bs) -> Method tp' additionalRegions args returnType returnRegions annotations b bs) <$ pWhitespace <*> pSome (pBlock quantors) pSep
    '=' -> do
      -- Shorthand for a function that computes a single expression and returns it
      pWhitespace
      expr <- pExpression quantors
      let result = idFromString "result"
      let b = Block (idFromString "entry") (Let result expr $ Return $ Local result $ typeToStrict returnType)
      return $ Method tp' additionalRegions args returnType returnRegions annotations b []
    _ -> pError "Expected '{' or '=' in a method declaration"
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace

      c <- lookahead
      if c == '}' then do
        pChar
        return False
      else
        return True
    toArg (Left quantor) = Left quantor
    toArg (Right (Local _ t)) = Right t

pMethodArguments :: QuantorNames -> Parser ([Either Quantor Local], QuantorNames)
pMethodArguments quantors = do
  (arg, quantors') <- pMethodArgument quantors
  pWhitespace
  c <- lookahead
  if c == ',' then do
    pChar
    pWhitespace
    (args, quantors'') <- pMethodArguments quantors'
    return (arg : args, quantors'')
  else
    return ([arg], quantors')

pMethodArgument :: QuantorNames -> Parser (Either Quantor Local, QuantorNames)
pMethodArgument quantors = do
  c <- lookahead
  case c of
    '%' -> do
      arg <- pLocal' (pType' quantors)
      return (Right arg, quantors)
    _ -> do
      pSymbol "forall"
      pWhitespace
      (quantor, quantors') <- pQuantor quantors
      return (Left quantor, quantors')

pBlock :: QuantorNames -> Parser Block
pBlock quantors = Block <$> pId <* pToken ':' <* pWhitespace <*> pInstruction quantors <* pWhitespace

pAbstractMethod :: Parser AbstractMethod
pAbstractMethod = do
  c <- lookahead
  case c of
    '[' -> do
      pToken '['
      pWhitespace
      arity <- pUnsignedInt
      pToken ']'
      pToken ':'
      pWhitespace
      pToken '{'
      pWhitespace
      tp <- pType
      fnType <- case extractFunctionTypeWithArityNoSynonyms arity tp of
        Nothing -> pError $ "Expected function type with arity at least " ++ show arity
        Just f -> return f
      pToken '}'
      pWhitespace
      AbstractMethod (typeRemoveArgumentStrictness tp) fnType <$> pAnnotations
    _ -> do
      pToken ':'
      pWhitespace
      pToken '{'
      pWhitespace
      sourceType <- pType
      pToken '}'
      pWhitespace
      pToken '$'
      pWhitespace
      pToken '['
      pWhitespace
      arity <- pUnsignedInt
      pToken ']'
      pWhitespace
      pToken '{'
      pWhitespace
      tp <- pType
      fnType <- case extractFunctionTypeWithArityNoSynonyms arity tp of
        Nothing -> pError $ "Expected function type with arity at least " ++ show arity
        Just f -> return f
      pToken '}'
      pWhitespace
      AbstractMethod sourceType fnType <$> pAnnotations

pAnnotations :: Parser [MethodAnnotation]
pAnnotations =
  do
    c <- lookahead
    if c == '[' then do
      pChar
      (isLong, annotation) <- pAnnotation True
      annotations <- if isLong then return [] else pMany (snd <$> pAnnotation False) pSep
      pToken ']'
      pWhitespace
      annotations' <- pAnnotations
      return $ annotation : annotations ++ annotations'
    else
      return []
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      return $ c /= ']'

pAnnotation :: Bool -> Parser (Bool, MethodAnnotation)
pAnnotation first = do
  word <- pWord
  pWhitespace
  case word of
    "trampoline" -> return (False, MethodAnnotateTrampoline)
    "callconvention" -> do
      pToken ':'
      conv <- pWord
      case conv of
        "c" -> return (False, MethodAnnotateCallConvention CCC)
        "fast" -> return (False, MethodAnnotateCallConvention CCFast)
        "preserve_most" -> return (False, MethodAnnotateCallConvention CCPreserveMost)
        _ -> pError $ "Unknown calling convention: " ++ show conv
    "implicit_io" -> return (False, MethodAnnotateImplicitIO)
    "regions"
      | first -> (\a -> (True, MethodAnnotateRegion a)) <$ pToken ':' <* pWhitespace <*> Region.pAnnotation Region.emptyNames
    _ -> pError $ "Unknown annotation: " ++ show word
