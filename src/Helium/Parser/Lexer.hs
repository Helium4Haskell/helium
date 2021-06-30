{-# LANGUAGE PatternGuards #-}
{-| Module      :  Lexer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Parser.Lexer
    ( lexer, strategiesLexer
    , Token, Lexeme(..)
    , lexemeLength
    , checkTokenStreamForClassOrInstance
    , module Helium.Parser.LexerMessage
    ) where


import Helium.Main.Args
import Helium.Parser.LexerMonad
import Helium.Parser.LexerMessage
import Helium.Parser.LexerToken
import Helium.StaticAnalysis.Messages.StaticErrors
import Text.ParserCombinators.Parsec.Pos
import Text.ParserCombinators.Parsec.Prim(Parser)
import Text.Parsec
import Helium.Utils.Utils(internalError, hole)

import Control.Monad(when, liftM)
import Data.Char(ord)
import Data.List(isPrefixOf)

lexer :: [Option] -> String -> [Char] -> Either LexerError ([Token], [LexerWarning])
lexer opts fileName input = runLexerMonad opts fileName (mainLexer input)

strategiesLexer :: [Option] -> String -> [Char] -> Either LexerError ([Token], [LexerWarning])
strategiesLexer opts fileName input = 
    case lexer opts fileName input of
        Left err -> Left err
        Right (thetokens, warnings) -> Right (reserveStrategyNames thetokens, warnings)
        
type Lexer = [Char] -> LexerMonad [Token]

mainLexer :: Lexer
mainLexer a =
  do useTutor <- elem UseTutor `liftM` getOpts
     mainLexer' useTutor a

mainLexer' :: Bool -> Lexer
mainLexer' _ [] = do
    checkBracketsAtEOF
    pos <- getPos
    return [(incSourceLine (setSourceColumn pos 0) 1, LexEOF)]

mainLexer' _ ('-':'-':cs) 
    | not (nextCharSatisfy isSymbol rest) = do
        incPos (2 + length minuses)
        lexOneLineComment rest
    where
        (minuses, rest) = span (== '-') cs

mainLexer' useTutor ('{':'-':'#':' ':'M':'U':'S':'T':'U':'S':'E':' ':'#':'-':'}':cs) | useTutor = 
   returnToken LexMustUse 15 mainLexer cs

mainLexer' useTutor ('{':'-':'#':' ':'F':'C':cs) | useTutor = do 
    pos <- getPos 
    lexCaseFeedbackComment "" pos cs

mainLexer' useTutor ('{':'-':'#':' ':'F':cs) | useTutor = do 
    pos <- getPos 
    incPos 5
    lexFeedbackComment "" pos cs 

mainLexer' useTutor ('{':'-':'#':' ':'E':'T':'A':' ':n:' ':'#':'-':'}':cs)
    | useTutor, myIsDigit n = do
    returnToken (LexEta n) 13 mainLexer cs

mainLexer' _ ('{':'-':cs) = do 
    pos <- getPos 
    incPos 2
    lexMultiLineComment [pos] 0 cs 
        
mainLexer' _ input@('\'':_) = 
    lexChar input

mainLexer' _ input@('"':_) = 
    lexString input

-- warn if we see something like ".2"
mainLexer' _ ('.':c:cs) 
    | myIsDigit c = do
        pos <- getPos
        lexerWarning (LooksLikeFloatNoDigits (takeWhile myIsDigit (c:cs))) pos
        returnToken (LexVarSym ".") 1 mainLexer (c:cs)
        
mainLexer' useTutor input@(c:cs) 
    | myIsLower c || c == '_' = -- variable or keyword
        lexName isLetter LexVar LexKeyword keywords input
    | myIsSpace c = do
        when (c == '\t') $ do
            pos <- getPos
            lexerWarning TabCharacter pos
        nextPos c 
        mainLexer cs        
    | myIsUpper c = -- constructor
            lexQualOrCon input
    | c == ':' = -- constructor operator
        lexName isSymbol LexConSym LexResConSym reservedConSyms input
    | useTutor, c == '?' = -- named hole
        lexName (\c1 -> isLetter c1 || c1 == '?') LexNamedHole
                (internalError "Lexer" "mainLexer'" "constructor") [] input
    | isSymbol c = -- variable operator
        lexName isSymbol LexVarSym LexResVarSym (if useTutor then hole : reservedVarSyms else reservedVarSyms) input
    | c `elem` "([{" = do
        openBracket c
        returnToken (LexSpecial c) 1 mainLexer cs
    | c `elem` ")]}" = do
        closeBracket c
        returnToken (LexSpecial c) 1 mainLexer cs
    | c `elem` specialsWithoutBrackets = 
        returnToken (LexSpecial c) 1 mainLexer cs
    | myIsDigit c = -- number
        lexIntFloat input
    | otherwise = do
        pos <- getPos
        lexerError (UnexpectedChar c) pos

lexName :: (Char -> Bool) -> (String -> Lexeme) -> 
                (String -> Lexeme) -> [String] -> Lexer
lexName predicate normal reserved reserveds cs = do
    let (name@(first:_), rest) = span predicate cs
        lexeme = if name `elem` reserveds
                 then reserved name 
                 else normal   name
    when ((isSymbol first || first == ':') && name `contains` "--") $ do
        pos <- getPos
        lexerWarning CommentOperator pos
    returnToken lexeme (length name) mainLexer rest


-- Parses any number of commas enclosed by parentheses
tupleParser :: Parser String
tupleParser = do
    x <- char '('
    y <- many (char ',')
    z <- char ')'
    return $ x : y ++ [z]

-- Parses any number of letters, '$' signs or tuples using tupleParser
qualOrConParser :: Parser String
qualOrConParser = p
    where p = fmap concat $ many (try tupleParser <|> many1 (satisfy isLetter <|> char '$'))

parserParsedRest :: Parser String -> Parser (String, String)
parserParsedRest p = do
    x <- p
    rest <- many anyChar
    return (x, rest)

lexQualOrCon :: Lexer
lexQualOrCon input = let
    firstLex = parse (parserParsedRest qualOrConParser) "" input
    in do
    let (name@(first:_), rest) = either (const ("",input)) id firstLex
    when ((isSymbol first || first == ':') && name `contains` "--") $ do
        pos <- getPos
        lexerWarning CommentOperator pos
    case rest of
        '.':x:rest' -> if myIsSpace x 
            then returnToken (LexCon name) (length name) mainLexer rest
            else returnToken (LexQual name) (length name + 1) mainLexer (x:rest')
        _ -> returnToken (LexCon name) (length name) mainLexer rest

contains :: Eq a => [a] -> [a] -> Bool
[] `contains` _ = False
xs@(_:rest) `contains` ys = ys `isPrefixOf` xs || rest `contains` ys

-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------

lexIntFloat :: Lexer
lexIntFloat input = do
    _ <- getPos
    let (digits, rest) = span myIsDigit input
    case rest of
        ('.':rest2@(next:_)) 
            | myIsDigit next -> do
                let (fraction, rest3) = span myIsDigit rest2
                    prefix = digits ++ "." ++ fraction
                lexMaybeExponent prefix LexFloat rest3
            | next /= '.' -> do
                pos <- getPos
                lexerWarning (LooksLikeFloatNoFraction digits) pos
                lexMaybeExponent digits LexInt rest
        _ ->
            lexMaybeExponent digits LexInt rest

lexMaybeExponent :: String -> (String -> Lexeme) -> Lexer
lexMaybeExponent prefix lexemeFun input = 
    case input of
        ('e':'+':rest) ->
            lexExponent (prefix ++ "e+") rest
        ('E':'+':rest) ->
            lexExponent (prefix ++ "E+") rest
        ('e':'-':rest) ->
            lexExponent (prefix ++ "e-") rest
        ('E':'-':rest) ->
            lexExponent (prefix ++ "E-") rest
        ('e':rest) ->
            lexExponent (prefix ++ "e") rest
        ('E':rest) ->
            lexExponent (prefix ++ "E") rest
        _ ->
            returnToken (lexemeFun prefix) (length prefix) mainLexer input

lexExponent :: String -> Lexer
lexExponent prefix input = do
    startPos <- getPos
    let posAtExponent = addPos (length prefix) startPos
        (exponentDigits, rest) = span myIsDigit input
    if null exponentDigits then
        lexerError MissingExponentDigits posAtExponent
     else do
        let text = prefix ++ exponentDigits
        returnToken (LexFloat text) (length text) mainLexer rest

-----------------------------------------------------------
-- Characters
-----------------------------------------------------------

lexChar :: Lexer
lexChar input = do 
    pos <- getPos
    case input of
        '\'':'\\':c:'\'':cs -> -- '\n' etc
            if c `elem` escapeChars then    
                returnToken (LexChar ['\\',c]) 4 mainLexer cs
            else
                lexerError IllegalEscapeInChar pos
        '\'':'\'':_ -> -- ''
            lexerError EmptyChar pos
        '\'':c:'\'':cs -> -- 'a' '%'
            if ord c >= 32 && ord c <= 126 then 
                returnToken (LexChar [c]) 3 mainLexer cs
            else
                lexerError IllegalCharInChar pos
        ['\''] -> -- ' at end of file
            lexerError EOFInChar pos
        ('\'':cs) -> -- if there is a name between single quotes, we give a hint that backquotes might be meant 
            let (ds, es) = span (/= '\'') cs
                ws = words ds
            in if not (null es) && head es == '\'' && length ws == 1 && isName (head ws) then
                    lexerError (NonTerminatedChar (Just (head ws))) pos
               else 
                    lexerError (NonTerminatedChar Nothing) pos
        _ -> internalError "Lexer" "lexChar" "unexpected characters"

lexString :: Lexer
lexString ('"':cs) = 
    lexStringChar "" cs
lexString _ = 
    internalError "Lexer" "lexString" "should start with \""

lexStringChar :: String -> Lexer
lexStringChar revSoFar input = do
    startPos <- getPos
    let curPos = addPos (length revSoFar + 1) startPos
    case input of
        [] -> 
            lexerError EOFInString startPos
        '\\':c:cs ->
            if c `elem` escapeChars then
                lexStringChar (c:'\\':revSoFar) cs
            else
                lexerError IllegalEscapeInString curPos
        '"':cs ->
            returnToken (LexString (reverse revSoFar)) 
                        (length revSoFar + 2) mainLexer cs
        '\n':_ ->
            lexerError NewLineInString startPos
        c:cs ->
            if ord c >= 32 && ord c <= 126 then
                lexStringChar (c:revSoFar) cs
            else
                lexerError IllegalCharInString curPos
                
nextCharSatisfy :: (Char -> Bool) -> String -> Bool
nextCharSatisfy _ []    = False
nextCharSatisfy p (c:_) = p c

returnToken :: Lexeme -> Int -> Lexer -> Lexer
returnToken lexeme width continue input = do
    pos <- getPos
    incPos width
    let theToken = (pos, lexeme) 
    theTokens <- continue input
    return (theToken:theTokens)
       
-----------------------------------------------------------
-- Comment
-----------------------------------------------------------

lexOneLineComment :: Lexer
lexOneLineComment input =
    case input of
        [] -> mainLexer []
        ('\n':cs) -> do
            nextPos '\n'
            mainLexer cs
        (c:cs) -> do
            nextPos c
            lexOneLineComment cs

lexMultiLineComment :: [SourcePos] -> Int -> Lexer
lexMultiLineComment starts level input =
    case input of 
        '-':'}':cs 
            | level == 0 -> do
                incPos 2
                mainLexer cs
            | otherwise ->  do
                incPos 2
                lexMultiLineComment (tail starts) (level - 1) cs
        '{':'-':cs -> do
            pos <- getPos
            lexerWarning (NestedComment (head starts)) pos
            incPos 2
            lexMultiLineComment (pos:starts) (level+1) cs
        c:cs -> do
            nextPos c
            lexMultiLineComment starts level cs
        [] -> 
            lexerError UnterminatedComment (head starts)
            -- at end-of-file show the most recently opened comment

lexFeedbackComment :: String -> SourcePos -> Lexer
lexFeedbackComment feedback start input =
    case input of 
        '#':'-':'}':cs ->
           returnToken (LexFeedback (reverse feedback)) 
                       (length feedback + 6) mainLexer cs
        c:cs -> do
            nextPos c            
            lexFeedbackComment (c:feedback) start cs
        [] -> 
            lexerError UnterminatedComment start

lexCaseFeedbackComment :: String -> SourcePos -> Lexer
lexCaseFeedbackComment feedback start input =
    case input of 
        '#':'-':'}':cs ->
            returnToken (LexCaseFeedback (reverse feedback)) 0 mainLexer cs
        c:cs ->
            -- nextPos c            
            lexCaseFeedbackComment (c:feedback) start cs
        [] -> 
            lexerError UnterminatedComment start
-----------------------------------------------------------
-- Utility functions
-----------------------------------------------------------

isSymbol :: Char -> Bool
isSymbol = (`elem` symbols)
                                  
isLetter :: Char -> Bool
isLetter '\'' = True
isLetter '_'  = True
isLetter c    = myIsAlphaNum c

-- write our own isLower.. so that we don't accept funny symbols
myIsLower :: Char -> Bool
myIsLower c = c >= 'a' && c <= 'z'

myIsUpper :: Char -> Bool
myIsUpper c = c >= 'A' && c <= 'Z'

myIsDigit :: Char -> Bool
myIsDigit c = c >= '0' && c <= '9'

myIsAlphaNum :: Char -> Bool
myIsAlphaNum c = myIsLower c || myIsUpper c || myIsDigit c

myIsSpace :: Char -> Bool
myIsSpace c = c == ' ' || c == '\n' || c == '\t' || c == '\r'

isName :: String -> Bool
isName [] = False
isName (hd:tl) = (myIsUpper hd || myIsLower hd) && all isLetter tl

-----------------------------------------------------------
-- Constants
-----------------------------------------------------------

escapeChars :: String
escapeChars = "\\nabfnrtv\"'"

symbols :: String
symbols = "!#$%&*+./<=>?@^|-~:\\"

keywords :: [String]
keywords = 
    [ "let", "in", "do", "where", "case", "of", "if"
    , "then", "else", "data", "type", "module", "import"
    , "infix", "infixl", "infixr", "_", "deriving"
    , "class", "instance", "default"
    , "dimension", "unit"
    , "derives", "with", "from"
    , "alias"
    , "newtype" -- not supported
    ]

reservedConSyms :: [String]
reservedConSyms =
    [ "::" ]

reservedVarSyms :: [String]
reservedVarSyms =
    [ "=>", "->", "<-", "..", "-", "-.", "@", "=", "\\", "|", "~", "*", "/", "^", "?" ]

specialsWithoutBrackets :: String
specialsWithoutBrackets = 
    ",`;" 

reserveStrategyNames :: [Token] -> [Token]
reserveStrategyNames = 
  map (\theToken@(pos, lexeme) -> case lexeme of 
                   LexVar s    | s `elem` strategiesKeywords -> (pos, LexKeyword s)
                   LexVarSym s | s == "=="                   -> (pos, LexResVarSym s)
                   LexConSym s | s == ":"                    -> (pos, LexResConSym s)
                   _ -> theToken
      )

strategiesKeywords :: [String]
strategiesKeywords = [ "phase", "constraints", "siblings", "never", "close", "disjoint" ]

 
checkTokenStreamForClassOrInstance :: [Token] -> Errors          
checkTokenStreamForClassOrInstance theTokens = concatMap f theTokens  
  where f (pos, LexKeyword "class")    = [ClassesAndInstancesNotAllowed (sourcePosToRange pos)] 
        f (pos, LexKeyword "instance") = [ClassesAndInstancesNotAllowed (sourcePosToRange pos)]
        f _ = []

