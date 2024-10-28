module Helium.CodeGeneration.Iridium.Parse.Parser where

import Helium.Lvm.Common.Id(Id, idFromString)
import Data.Maybe

data ParseResult p = ResError !String !String | ResValue !p !String

-- A greedy parser with 1 character lookahead
newtype Parser p = Parser { runParser :: String -> ParseResult p }

instance Functor Parser where
  fmap f (Parser fn) = Parser (\source -> case fn source of
      ResError err remaining -> ResError err remaining
      ResValue x remaining -> ResValue (f x) remaining
    )

instance Applicative Parser where
  pure x = Parser $ ResValue x
  Parser fn1 <*> Parser fn2 = Parser (\source -> case fn1 source of
      ResError err remaining -> ResError err remaining
      ResValue f remaining -> case fn2 remaining of
        ResError err remaining' -> ResError err remaining'
        ResValue x remaining' -> ResValue (f x) remaining'
    )

instance Monad Parser where
  return = pure
  Parser fn1 >>= p = Parser (\source -> case fn1 source of
      ResError err remaining -> ResError err remaining
      ResValue x remaining ->
        let Parser fn2 = p x
        in fn2 remaining
    )

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace '\n' = True
isWhitespace '\r' = True
isWhitespace '\t' = True
isWhitespace _ = False

pError :: String -> Parser a
pError err = Parser $ ResError err

pMaybe :: Parser a -> Parser (Maybe a)
pMaybe (Parser p) = Parser f
  where
    f str = case p str of
      ResError _ _ -> ResValue Nothing str
      ResValue v str' -> ResValue (Just v) str'

pManyMaybe :: Parser (Maybe a) -> Parser [a]
pManyMaybe p = do
  res <- p
  case res of
    Just x -> (x : ) <$> pManyMaybe p
    Nothing -> return []

validWordChar :: Char -> Bool
validWordChar c = ('a' <= c && c <= 'z') || c == '_'

pKeyword :: Parser String
pKeyword = Parser f
  where
    f str =
      let
        (parsed, remaining) = span validWordChar str
        (spaces, remaining') = span isWhitespace remaining
      in case parsed of
        [] -> ResError "expected keyword" str
        _ -> case spaces of
          [] -> ResError "expected whitespace after keyword" remaining
          _ -> ResValue parsed remaining'

pWord :: Parser String
pWord = pManySatisfy validWordChar

lookahead :: Parser Char
lookahead = Parser f
  where
    f [] = ResValue '\0' ""
    f str@(c : _) = ResValue c str

isEndOfFile :: Parser Bool
isEndOfFile = Parser f
  where
    f str = ResValue (null str) str

-- Reads a single character
pChar :: Parser Char
pChar = Parser f
  where
    f [] = ResError "unexpected EOF while reading a single character" []
    f (c : str) = ResValue c str

pToken :: Char -> Parser ()
pToken t = Parser f
  where
    f (c : str)
      | c == t = ResValue () str
    f str = ResError ("expected " ++ show t) str

pSymbol :: String -> Parser ()
pSymbol sym = Parser f
  where
    f str
      | compare == sym = ResValue () remaining
      | otherwise = ResError ("expected " ++ sym) str
      where
        (compare, remaining) = splitAt (length sym) str

pSomeSatisfy :: String -> (Char -> Bool) -> Parser String
pSomeSatisfy err fn = do
  str <- pManySatisfy fn
  if null str then
    pError err
  else
    return str

pManySatisfy :: (Char -> Bool) -> Parser String
pManySatisfy fn = Parser f
  where
    f str =
      let
        (parsed, remaining) = span fn str
      in ResValue parsed remaining

pSome :: Parser a -> Parser Bool -> Parser [a]
pSome elem continue = do
  item <- elem
  c <- continue
  if c then
    (item :) <$> pSome elem continue
  else
    return [item]

pWhitespace :: Parser ()
pWhitespace = 
  do
    pManySatisfy isWhitespace
    c <- lookahead
    if c == ';' then do
      pChar
      pManySatisfy (/= '\n')
      pWhitespace
    else return ()

pString :: Parser String
pString = read <$> Parser f
  where
    f ('"' : str) = prepend '"' $ g str
    f str = ResError "expected string" str
    g :: String -> ParseResult String
    g ('\\' : c : str) = prepend '\\' $ prepend c $ g str
    g ('"' : str) = ResValue "\"" str
    g (c : str) = prepend c $ g str
    g [] = ResError "unexpected EOF while parsing a string" []
    prepend :: Char -> ParseResult String -> ParseResult String
    prepend c (ResValue str remaining) = ResValue (c : str) remaining
    prepend _ r = r

pId :: Parser Id
pId = idFromString <$> pName

pName :: Parser String
pName = do
    c <- lookahead
    if c == '"' then
      pString
    else
      pSomeSatisfy "expected name" valid
  where
    valid c
      = ('a' <= c && c <= 'z')
      || ('A' <= c && c <= 'Z')
      || ('0' <= c && c <= '9')
      || c == '$' || c == '.' || c == '_' || c == '#'

pUnsignedInt :: Parser Int
pUnsignedInt = do
    str <- pManySatisfy valid
    if str == "" then
      pError "expected integer"
    else
      return $ read str
  where
    valid c = '0' <= c && c <= '9'

pSignedInt :: Parser Int
pSignedInt = do
  c <- lookahead
  if c == '-' then do
    pChar
    (0 -) <$> pUnsignedInt
  else
    pUnsignedInt

pArguments :: Parser a -> Parser [a]
pArguments pArg = do
  pToken '('
  c <- lookahead
  if c == ')' then do
    pChar
    return []
  else
    pWhitespace *> pSome pArg pSep <* pToken ')'
  where
    pSep :: Parser Bool
    pSep = do
      pWhitespace
      c <- lookahead
      if c == ',' then do
        pChar
        pWhitespace
        return True
      else
        return False

data ParseError = ParseError !Int !Int String

instance Show ParseError where
  show (ParseError line col err)
    = "Parse error at line " ++ show line ++ ", column " ++ show col ++ ":"
    ++ "\n  " ++ err

parse :: Parser a -> String -> Either ParseError a
parse (Parser parser) source = case parser source of
  ResValue a _ -> Right a
  ResError err remaining ->
    let 
      consumed = take (length source - length remaining) source
      line = length $ filter (== '\n') consumed
      column = length $ takeWhile (/= '\n') $ reverse consumed
    in
      Left $ ParseError (line + 1) (column + 1) err
