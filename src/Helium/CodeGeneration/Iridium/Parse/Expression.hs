module Helium.CodeGeneration.Iridium.Parse.Expression where

import Control.Applicative
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Parse.Parser
import Helium.CodeGeneration.Iridium.Parse.Type
import Lvm.Core.Type
import qualified Text.Parsec as P

pLiteral :: Parser Literal
pLiteral =
  LitInt IntTypeInt <$ pSymbol "int" <*> pSignedInt
    <|> LitInt IntTypeChar
    <$ pSymbol "char" <*> pSignedInt
    <|> LitFloat
    <$ pSymbol "float" <*> pFloatPrecision
      <*> pFloat
    <|> LitString
    <$ pSymbol "str" <*> pString

pGlobal :: Parser Global
pGlobal = pNamedTypeAtom GlobalVariable

pGlobalFunction :: Parser GlobalFunction
pGlobalFunction = GlobalFunction <$ pToken '@' <*> pId <*> pBrackets pUnsignedInt <* pToken ':' <*> pTypeAtom

pLocal :: Parser Local
pLocal = Local <$ pToken '%' <*> pId <* pToken ':' <*> pTypeAtom

pVariable :: Parser Variable
pVariable = VarGlobal <$> pGlobal <|> VarLocal <$> pLocal

pArguments :: Parser a -> Parser [a]
pArguments pArg = pParentheses (P.sepBy pArg (pToken ','))

pCallArguments :: Parser [Either Type Variable]
pCallArguments = pArguments pCallArgument
  where
    pCallArgument = Left <$> pBraces pType <|> Right <$> pVariable

pExpression :: Parser Expr
pExpression =
  Call <$ P.try (pSymbol "call") <*> pGlobalFunction <* pToken '$' <*> pCallArguments
    <|> CastThunk <$ P.try (pSymbol "castthunk") <*> pVariable
    <|> Cast <$ pSymbol "cast" <*> pVariable <* pSymbol "as"  <*> pTypeAtom
    <|> Eval <$ pSymbol "eval" <*> pVariable
    <|> Instantiate <$ pSymbol "instantiate" <*> pVariable <*> pInstantiation
    <|> Literal <$ pSymbol "literal" <*> pLiteral
    <|> Phi <$ P.try (pSymbol "phi") <*> pArguments pPhiBranch
    <|> PrimitiveExpr <$ pSymbol "prim" <*> pId <*> pCallArguments
    <|> Seq <$ pSymbol "seq" <*> pVariable <* pToken ',' <*> pVariable
    <|> Undefined <$ pSymbol "undefined" <*> pTypeAtom
    <|> Var <$ pSymbol "var" <*> pVariable

pPhiBranch :: Parser PhiBranch
pPhiBranch = PhiBranch <$> pId <* pSymbol "=>" <*> pVariable
