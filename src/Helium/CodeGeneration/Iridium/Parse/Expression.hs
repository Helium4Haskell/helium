module Helium.CodeGeneration.Iridium.Parse.Expression where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Lvm.Core.Type

pLiteral :: Parser Literal
pLiteral = do
  keyword <- pWord
  case keyword of
    "int" -> LitInt IntTypeInt <$ pWhitespace <*> pSignedInt
    "char" -> LitInt IntTypeChar <$ pWhitespace <*> pSignedInt
    "float" -> LitFloat <$> pFloatPrecision <* pWhitespace <*> pFloat
    "str" -> LitString <$ pWhitespace <*> pString
    _ -> pError "expected literal"

pFloat :: Parser Double
pFloat = do
  cMinus <- lookahead
  sign <- case cMinus of
    '-' -> do
      pChar
      return (-1)
    _ -> return 1
  int <- pUnsignedInt
  c <- lookahead
  case c of
    '.' -> do
      pChar
      decimalStr <- pManySatisfy (\c -> '0' <= c && c <= '9')
      let decimal = foldl (+) 0 $ zipWith (\c i -> fromIntegral (fromEnum c - fromEnum '0') / (10 ^ i)) decimalStr [1..]
      let value = sign * fromIntegral int + decimal
      c2 <- lookahead
      if c2 == 'e' then do
        pChar
        exp <- pSignedInt
        return $ value * 10 ^ exp
      else
        return value
    'e' -> do
      pChar
      exp <- pSignedInt
      return $ sign * fromIntegral int * 10 ^ exp
    _ -> return $ sign * fromIntegral int

pGlobal :: QuantorIndexing -> Parser Global
pGlobal quantors = do
  pToken '@'
  name <- pId
  pToken ':'
  pWhitespace
  GlobalVariable name <$> pTypeAtom

pGlobalFunction :: QuantorIndexing -> Parser GlobalFunction
pGlobalFunction quantors = do
  pToken '@'
  name <- pId
  pWhitespace
  pToken '['
  pWhitespace
  arity <- pUnsignedInt
  pWhitespace
  pToken ']'
  pWhitespace
  pToken ':'
  pWhitespace
  tp <- pTypeAtom' quantors
  return $ GlobalFunction name arity tp

pLocal :: QuantorIndexing -> Parser Local
pLocal quantors = Local <$ pToken '%' <*> pId <* pToken ':' <* pWhitespace <*> pTypeAtom' quantors

pVariable :: QuantorIndexing -> Parser Variable
pVariable quantors = do
  c <- lookahead
  case c of
    '@' -> VarGlobal <$> pGlobal quantors
    '%' -> VarLocal <$> pLocal quantors
    _ -> pError "expected variable"

pCallArguments :: QuantorIndexing -> Parser [Either Type Variable]
pCallArguments quantors = pArguments pCallArgument
  where
    pCallArgument = do
      c <- lookahead
      if c == '{' then
        Left <$ pChar <* pWhitespace <*> pType' quantors <* pToken '}'
      else
        Right <$> pVariable quantors

pExpression :: QuantorIndexing -> Parser Expr
pExpression quantors = do
  keyword <- pKeyword
  case keyword of
    "literal" -> Literal <$> pLiteral
    "call" -> Call <$> pGlobalFunction quantors <* pWhitespace <* pToken '$' <* pWhitespace <*> pCallArguments quantors
    "eval" -> Eval <$> pVariable quantors
    "var" -> Var <$> pVariable quantors
    "instantiate" -> Instantiate <$> pVariable quantors <* pWhitespace <*> pInstantiation quantors
    -- "cast" -> Cast <$> pVariable quantors <* pWhitespace <* pSymbol "as" <* pWhitespace <*> pTypeAtom' quantors
    "castthunk" -> CastThunk <$> pVariable quantors
    "phi" -> Phi <$> pArguments (pPhiBranch quantors)
    "prim" -> PrimitiveExpr <$> pId <* pWhitespace <*> pCallArguments quantors
    "undefined" -> Undefined <$ pWhitespace <*> pTypeAtom' quantors
    "seq" -> Seq <$> pVariable quantors <* pWhitespace <* pToken ',' <* pWhitespace <*> pVariable quantors
    _ -> pError "expected expression"

pPhiBranch :: QuantorIndexing -> Parser PhiBranch
pPhiBranch quantors = PhiBranch <$> pId <* pWhitespace <* pSymbol "=>" <* pWhitespace <*> pVariable quantors
