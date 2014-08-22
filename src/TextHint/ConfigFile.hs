module TextHint.ConfigFile (
        Config, 
        readConfig, 
        extractOptions, 
        configFilename, 
        temppathKey,
        unknown,
        passToHelium,
        trim) where


import Control.Monad
import Data.Char
import Data.Maybe
import Text.ParserCombinators.Parsec

import Helium.Main.Args

type Config = [(String,String)]

-- Constants for configuration files
configFilename :: String
configFilename = "hint.conf" 
temppathKey    :: String
temppathKey    = "temppath"
unknown        :: String
unknown        = "<unknown>"
passToHelium   :: [String]
passToHelium   = ["overloadingon", "loggingon", "host", "port",
                  "lvmpaths", "additionalheliumparameters"]
                 
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
          try (comment >> return Nothing) <|> liftM Just item
          
file :: Parser [(String, String)]
file = do ls <- many line
          return (catMaybes ls)

readConfig :: SourceName -> IO Config
readConfig name = do{ result <- parseFromFile file name
                    ; case result of
                       Left err  -> do{ print err
                                      ; putStrLn "Error"
                                      ; return []
                                      }
                       Right xs  -> return (reverse xs) 
                    }

extractOptions :: Config -> [String]
extractOptions []         = []
extractOptions ((k,v):xs) = 
  if k `elem` passToHelium then
      tfm k : rest
  else
      rest
   where
     rest = extractOptions xs
     tfm x = case x of 
               "overloadingon"
                  | v == "false" -> show NoOverloading
                  | otherwise    -> show Overloading
               "loggingon"
                  | v == "false" -> show DisableLogging
                  | otherwise    -> show EnableLogging
               "host"            -> show (Host v)
               "port"            -> show (Port (read v))
               "lvmpaths"
                  | trim v == "" -> ""  
                  | otherwise    -> show (LvmPath v)
               "additionalheliumparameters" -> v
               _ -> error "Internal error in RunHelium/Main.hs"


trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace


