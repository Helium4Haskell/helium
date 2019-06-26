module Helium.CodeGeneration.Iridium.Parse.Method where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import qualified Helium.CodeGeneration.Iridium.Region.AnnotationParser as Region
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
  pToken '('
  pWhitespace
  let emptyQuantors = QuantorIndexing 0 [] []
  c <- lookahead
  (args, quantors) <-
    if c == ')' then
      return ([], emptyQuantors)
    else
      pMethodArguments (QuantorIndexing 0 [] [])
  pToken ')'
  pWhitespace
  pToken ':'
  pWhitespace
  returnType <- pType' quantors
  annotations <- pAnnotations
  pWhitespace
  c <- pChar
  let tp' = fromMaybe (typeFromFunctionType $ FunctionType (map toArg args) returnType) tp
  case c of
    '{' ->
      (\(b:bs) -> Method tp' args returnType annotations b bs) <$ pWhitespace <*> pSome (pBlock quantors) pSep
    '=' -> do
      -- Shorthand for a function that computes a single expression and returns it
      pWhitespace
      expr <- pExpression quantors
      annotations <- pAnnotations
      let result = idFromString "result"
      let b = Block (idFromString "entry") (Let result expr $ Return $ VarLocal $ Local result $ typeToStrict returnType)
      return $ Method tp' args returnType annotations b []
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

pMethodArguments :: QuantorIndexing -> Parser ([Either Quantor Local], QuantorIndexing)
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

pMethodArgument :: QuantorIndexing -> Parser (Either Quantor Local, QuantorIndexing)
pMethodArgument quantors = do
  c <- lookahead
  case c of
    '%' -> do
      arg <- pLocal quantors
      return (Right arg, quantors)
    _ -> do
      pSymbol "forall"
      pWhitespace
      (quantor, quantors') <- pQuantor quantors
      return (Left quantor, quantors')

pBlock :: QuantorIndexing -> Parser Block
pBlock quantors = Block <$> pId <* pToken ':' <* pWhitespace <*> pInstruction quantors <* pWhitespace

pAbstractMethod :: Parser AbstractMethod
pAbstractMethod = AbstractMethod <$ pToken '[' <* pWhitespace <*> pUnsignedInt <* pToken ']' <* pToken ':' <* pWhitespace <* pToken '{' <* pWhitespace <*> pType <* pToken '}' <* pWhitespace <*> pAnnotations

pAnnotations :: Parser [MethodAnnotation]
pAnnotations =
  do
    eof <- isEndOfFile
    if eof then
      return []
    else do
      c <- lookahead
      if c == '[' then pToken '[' *> pSome pMethodAnnotation pSep <* pToken ']' else return []
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      return $ c /= ']'

pMethodAnnotation :: Parser MethodAnnotation
pMethodAnnotation = do
  word <- pWord
  pWhitespace
  case word of
    "trampoline" -> return MethodAnnotateTrampoline
    "callconvention" -> do
      pToken ':'
      conv <- pWord
      case conv of
        "c" -> return $ MethodAnnotateCallConvention CCC
        "fast" -> return $ MethodAnnotateCallConvention CCFast
        "preserve_most" -> return $ MethodAnnotateCallConvention CCPreserveMost
        _ -> pError $ "Unknown calling convention: " ++ show conv
    "fake_io" -> return MethodAnnotateFakeIO
    "region" -> MethodAnnotateRegion <$ pToken ':' <*> Region.pArgument Region.pAnnotation
    _ -> pError $ "Unknown annotation: " ++ show word
