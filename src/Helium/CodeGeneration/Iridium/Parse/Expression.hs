module Helium.CodeGeneration.Iridium.Parse.Expression where

import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Helium.CodeGeneration.Iridium.Data

instance Show Literal where
  show (LitInt x) = "int " ++ show x
  show (LitDouble x) = "float " ++ show x
  show (LitString x) = "str " ++ show x

pLiteral :: Parser Literal
pLiteral = do
  keyword <- pKeyword
  case keyword of
    "int" -> LitInt <$> pInt
    "float" -> pError "floats are not yet supported"
    "str" -> LitString <$> pString
    _ -> pError "expected literal"

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
    _ -> pError "expected expression"

pPhiBranch :: Parser PhiBranch
pPhiBranch = PhiBranch <$> pId <* pWhitespace <* pSymbol "=>" <* pWhitespace <*> pVariable
