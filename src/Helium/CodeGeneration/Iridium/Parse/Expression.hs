module Helium.CodeGeneration.Iridium.Parse.Expression where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.Lvm.Core.Type

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

pGlobal :: Parser Global
pGlobal = do
  pToken '@'
  name <- pId
  pToken ':'
  pWhitespace
  GlobalVariable name <$> pTypeAtom

pGlobalFunction :: Parser GlobalFunction
pGlobalFunction = do
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
  tp <- pTypeAtom
  return $ GlobalFunction name arity tp

pLocal :: Parser Type -> Parser Local
pLocal pTp = Local <$ pToken '%' <*> pId <* pToken ':' <* pWhitespace <*> pTp

pVariable :: QuantorNames -> Parser Variable
pVariable quantors = do
  c <- lookahead
  case c of
    '@' -> VarGlobal <$> pGlobal
    '%' -> VarLocal <$> pLocal (pTypeAtom' quantors)
    _ -> pError "expected variable"

pCallArguments :: QuantorNames -> Parser [Either Type Variable]
pCallArguments quantors = pArguments pCallArgument
  where
    pCallArgument = do
      c <- lookahead
      if c == '{' then
        Left <$ pChar <* pWhitespace <*> pType' quantors <* pToken '}'
      else
        Right <$> pVariable quantors

pExpression :: QuantorNames -> Parser Expr
pExpression quantors = do
  keyword <- pKeyword
  case keyword of
    "literal" -> Literal <$> pLiteral
    "call" -> Call <$> pGlobalFunction <* pWhitespace <* pToken '$' <* pWhitespace <*> pCallArguments quantors
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

pPhiBranch :: QuantorNames -> Parser PhiBranch
pPhiBranch quantors = PhiBranch <$> pId <* pWhitespace <* pSymbol "=>" <* pWhitespace <*> pVariable quantors
