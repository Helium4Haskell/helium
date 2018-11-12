module Helium.CodeGeneration.Iridium.Parse.Method where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Parse.Instruction
import Helium.CodeGeneration.Iridium.Parse.Expression
import Helium.CodeGeneration.Iridium.Data

pMethod :: Parser Method
pMethod = (\args rettype annotations (b:bs) -> Method args rettype annotations b bs) <$> pArguments pLocal <* pToken ':' <* pWhitespace <*> pType <* pWhitespace <*> pAnnotations <* pWhitespace <* pToken '{' <* pWhitespace <*> pSome pBlock pSep
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
pAnnotations = pToken '[' *> pSome pAnnotation pSep <* pToken ']'
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      return $ c /= '/'

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
    _ -> pError $ "Unknown annotation: " ++ show word
