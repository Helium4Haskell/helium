module Helium.CodeGeneration.Iridium.Parse.Parser where

import Lvm.Common.Id(Id, idFromString)

-- A greedy parser with 1 character lookahead
newtype Parser p = Parser { runParser :: (String -> (Either String p, String)) }

instance Functor Parser where
  fmap f (Parser fn) = Parser (\source -> case fn source of
      (Left err, remaining) -> (Left err, remaining)
      (Right x, remaining) -> (Right $ f x, remaining)
    )

instance Applicative Parser where
  pure x = Parser (\source -> (Right x, source))
  Parser fn1 <*> Parser fn2 = Parser (\source -> case fn1 source of
      (Left err, remaining) -> (Left err, remaining)
      (Right f, remaining) -> case fn2 remaining of
        (Left err, remaining') -> (Left err, remaining')
        (Right x, remaining') -> (Right $ f x, remaining')
    )

instance Monad Parser where
  return = pure
  Parser fn1 >>= p = Parser (\source -> case fn1 source of
      (Left err, remaining) -> (Left err, remaining)
      (Right x, remaining) ->
        let Parser fn2 = p x
        in fn2 remaining
    )

isWhitespace :: Char -> Bool
isWhitespace ' ' = True
isWhitespace '\n' = True
isWhitespace '\t' = True
isWhitespace _ = False

pError :: String -> Parser a
pError err = Parser (\s -> (Left err, s))

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
        [] -> (Left "expected keyword", str)
        _ -> case spaces of
          [] -> (Left "expected whitespace after keyword", remaining)
          _ -> (Right parsed, remaining')

pWord :: Parser String
pWord = pManySatisfy validWordChar

lookahead :: Parser Char
lookahead = Parser f
  where
    f [] = (Left "unexpected EOF", [])
    f str@(c : _) = (Right c, str)

isEndOfFile :: Parser Bool
isEndOfFile = Parser f
  where
    f str = (Right $ null str, str)

-- Reads a single character
pChar :: Parser Char
pChar = Parser f
  where
    f [] = (Left "unexpected EOF", [])
    f (c : str) = (Right c, str)

pToken :: Char -> Parser ()
pToken t = Parser f
  where
    f (c : str)
      | c == t = (Right (), str)
    f str = (Left $ "expected " ++ show t, str)

pSymbol :: String -> Parser ()
pSymbol sym = Parser f
  where
    f str
      | compare == sym = (Right (), remaining)
      | otherwise = (Left $ "expected " ++ sym, str)
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
      in (Right parsed, remaining)

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
    f str = (Left "expected string", str)
    g :: String -> (Either String String, String)
    g ('\\' : c : str) = prepend '\\' $ prepend c $ g str
    g ('"' : str) = (Right "\"", str)
    g (c : str) = prepend c $ g str
    g [] = (Left "unexpected EOF", [])
    prepend :: Char -> (Either String String, String) -> (Either String String, String)
    prepend c (Right str, remaining) = (Right $ c : str, remaining)
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
      || c == '$' || c == '.' || c == '_'

pInt :: Parser Int
pInt = do
    str <- pManySatisfy valid
    if str == "" then
      pError "expected integer"
    else
      return $ read str
  where
    valid c = '0' <= c && c <= '9'

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
  (Right a, _) -> Right a
  (Left err, remaining) ->
    let 
      consumed = take (length source - length remaining) source
      line = length $ filter (== '\n') consumed
      column = length $ takeWhile (/= '\n') $ reverse consumed
    in
      Left $ ParseError (line + 1) (column + 1) err
