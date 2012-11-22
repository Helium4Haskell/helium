module TextHint.ConfigFile (Config, readConfig) where


import Data.Char

-- import qualified Data.Map as Map
import Text.ParserCombinators.Parsec
--import Data.Either
import Data.Maybe

type Config = [(String,String)]

-- Thanks to Bryan OÕSullivan, I might upgrade this later to something more in
-- the style of the Helium parser.
-- TODO deal with empty lines AT THE END of the config file.
ident :: Parser String
ident = do c  <- letter <|> char '_'
           cs <- many (letter <|> digit <|> char '_')
           return (c:cs)
        <?> "identifier"
 
comment :: Parser ()
comment = do _ <- char '#'
             skipMany (noneOf "\r\n")
        <?> "comment"

{- 
eol :: Parser ()
eol = do oneOf "\n\r"
         return ()
      <?> "end of line"
-}

item :: Parser (String, String)
item = do key <- ident
          skipMany space
          _ <- char '='
          value <- many (noneOf "\n\r")
          _ <- newline
          return (key, strip value)
    where strip = reverse . dropWhile isSpace . reverse . dropWhile isSpace 

line :: Parser (Maybe (String, String))
line = do skipMany space
          try (comment >> return Nothing) <|> (item >>= return . Just)
          
file :: Parser [(String, String)]
file = do ls <- many line
          return (catMaybes ls)

readConfig :: SourceName -> IO Config
readConfig name = do{ result <- parseFromFile file name
                    ; case (result) of
                       Left err  -> do{ print err
                                      ; putStrLn "Error"
                                      ; return []
                                      }
                       Right xs  -> return (reverse xs) 
                    }

