module Helium.CodeGeneration.Iridium.Parse.Expression where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type

pLiteral :: Parser Literal
pLiteral = do
  keyword <- pWord
  case keyword of
    "int" -> LitInt <$ pWhitespace <*> pSignedInt
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

pGlobal :: Parser Global
pGlobal = do
  pToken '@'
  name <- pId
  pToken ':'
  pWhitespace
  c <- lookahead
  case c of
    '(' -> GlobalFunction name <$> pFunctionType
    _ -> GlobalVariable name <$> pType

pLocal :: Parser Local
pLocal = Local <$ pToken '%' <*> pId <* pToken ':' <* pWhitespace <*> pType

pVariable :: Parser Variable
pVariable = do
  c <- lookahead
  case c of
    '@' -> VarGlobal <$> pGlobal
    '%' -> VarLocal <$> pLocal
    _ -> pError "expected variable"

pExpression :: Parser Expr
pExpression = do
  keyword <- pKeyword
  case keyword of
    "literal" -> Literal <$> pLiteral
    "call" -> Call <$> pGlobal <* pWhitespace <* pToken '$' <* pWhitespace <*> pArguments pVariable
    "eval" -> Eval <$> pVariable
    "var" -> Var <$> pVariable
    "cast" -> Cast <$> pVariable <* pWhitespace <* pSymbol "as" <* pWhitespace <*> pType
    "phi" -> Phi <$> pArguments pPhiBranch
    "prim" -> PrimitiveExpr <$> pId <* pWhitespace <*> pArguments pVariable
    "undefined" -> Undefined <$ pWhitespace <*> pType
    "seq" -> Seq <$> pVariable <* pWhitespace <* pToken ',' <* pWhitespace <*> pVariable
    _ -> pError "expected expression"

pPhiBranch :: Parser PhiBranch
pPhiBranch = PhiBranch <$> pId <* pWhitespace <* pSymbol "=>" <* pWhitespace <*> pVariable
