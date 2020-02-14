module Helium.CodeGeneration.Iridium.Parse.Parser where

import Control.Applicative
import Data.Char
import Data.Functor.Identity
import Lvm.Common.Id (Id, idFromString)
import qualified Text.Parsec as P
import Text.Parsec.Language (emptyDef)
import qualified Text.Parsec.Token as P

type Parser a = P.Parsec String () a

lexer :: P.GenTokenParser String () Identity
lexer =
  P.makeTokenParser
    emptyDef
      { P.commentLine = ";"
      }

pWord :: Parser String
pWord = P.many1 P.letter

pToken :: Char -> Parser Char
pToken = pLexeme . P.char

pSymbol :: String -> Parser String
pSymbol = pLexeme . P.string

pBraces :: Parser a -> Parser a
pBraces = P.braces lexer

pParentheses :: Parser a -> Parser a
pParentheses = P.parens lexer

pBrackets :: Parser a -> Parser a
pBrackets = P.brackets lexer

pSome :: Parser a -> Parser [a]
pSome = P.many1

pLexeme :: Parser p -> Parser p
pLexeme = P.lexeme lexer

pWhitespace :: Parser ()
pWhitespace = P.skipMany1 (P.satisfy isSpace)

pComment :: Parser ()
pComment = P.try (pToken ';') *> P.skipMany (P.satisfy (/= '\n'))

pId :: Parser Id
pId = idFromString <$> pName

pString :: Parser String
pString = P.stringLiteral lexer

pName :: Parser String
pName = pLexeme (pString <|> pSome (P.satisfy valid))
  where
    valid c =
      isAlphaNum c
        || c == '$'
        || c == '.'
        || c == '_'
        || c == '#'

number :: Parser Int
number = fromIntegral <$> P.decimal lexer

pFloat :: Parser Double
pFloat = P.float lexer

pUnsignedInt :: Parser Int
pUnsignedInt = pLexeme $ fromIntegral <$> number

pSignedInt :: Parser Int
pSignedInt = fromIntegral <$> P.integer lexer
