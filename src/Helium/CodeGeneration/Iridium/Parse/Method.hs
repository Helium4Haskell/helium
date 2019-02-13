module Helium.CodeGeneration.Iridium.Parse.Method where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id(Id, idFromString)

pMethod :: Parser Method
pMethod = do
  args <- pArguments pLocal
  pWhitespace
  c <- pChar
  case c of
    ':' ->
      (\rettype annotations (b:bs) -> Method args rettype annotations b bs) <$ pWhitespace <*> pType <* pWhitespace <*> pAnnotations <* pWhitespace <* pToken '{' <* pWhitespace <*> pSome pBlock pSep
    '=' -> do
      -- Shorthand for a function that computes a single expression and returns it
      pWhitespace
      expr <- pExpression
      annotations <- pAnnotations
      let result = idFromString "result"
      let returnType = typeOfExpr expr 
      let b = Block (idFromString "entry") (Let result expr $ Return $ VarLocal $ Local result returnType)
      return $ Method args returnType annotations b []
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

pBlock :: Parser Block
pBlock = Block <$> pId <* pToken ':' <* pWhitespace <*> pInstruction <* pWhitespace

pAbstractMethod :: Parser AbstractMethod
pAbstractMethod = AbstractMethod <$ pToken ':' <* pWhitespace <*> pFunctionType <* pWhitespace <*> pAnnotations

pAnnotations :: Parser [Annotation]
pAnnotations =
  do
    eof <- isEndOfFile
    if eof then
      return []
    else do
      c <- lookahead
      if c == '[' then pToken '[' *> pSome pAnnotation pSep <* pToken ']' else return []
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      return $ c /= ']'

pAnnotation :: Parser Annotation
pAnnotation = do
  word <- pWord
  pWhitespace
  case word of
    "trampoline" -> return AnnotateTrampoline
    "callconvention" -> do
      pToken ':'
      conv <- pWord
      case conv of
        "c" -> return $ AnnotateCallConvention CCC
        "fast" -> return $ AnnotateCallConvention CCFast
        "preserve_most" -> return $ AnnotateCallConvention CCPreserveMost
        _ -> pError $ "Unknown calling convention: " ++ show conv
    "fake_io" -> return AnnotateFakeIO
    _ -> pError $ "Unknown annotation: " ++ show word
