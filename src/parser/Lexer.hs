module Lexer
    ( Token, Lexeme(..), Pos(..)
    , lexer
    , layout
    , lexemeLength
    , charErrors, stringErrors, floatErrors, commentErrors
    ) where

import Char

-----------------------------------------------------------
-- The layout rule
-----------------------------------------------------------

layout :: [Token] -> [Token]
layout input@((pos@(Pos _ col), lexeme):_) = optimise $
    case lexeme of 
        LexKeyword "module" -> 
            lay (Pos 0 0) [] input
        LexSpecial '{' ->
            lay (Pos 0 0) [] input
        _ ->
            (pos, LexINSERTED_LBRACE) : lay (Pos 0 0) [CtxLay col False] input
layout [] = []

optimise :: [Token] -> [Token]
optimise (token1@(_, LexINSERTED_LBRACE) : (_, LexINSERTED_SEMI) : ts) =
    optimise (token1 : ts)
optimise (t:ts) = 
    t : optimise ts
optimise [] = []

data Context 
    = CtxLay Int Bool {- let? -}
    | CtxBrace
    deriving (Eq,Show)
    
--  position previous token
--            enclosing contexts
lay :: Pos -> [Context] -> [Token] -> [Token]

-- If we're in a CtxBrace and we see a '}', we leave that context.
-- If we see another token, we check to see if we need to add a
-- new context.
lay     prev 
        cc@(CtxBrace:cs) 
        input@(t@(pos, lexeme):ts)
    | lexeme == LexSpecial '}' =
        t : lay pos cs ts
    | otherwise = 
        t : addContext pos cc input 

-- If we're in a let layout context, an 'in' can end
-- the context, too.
lay     _ 
        (CtxLay _ True:cs) 
        (t@(pos, LexKeyword "in"):ts) 
    = (pos, LexINSERTED_RBRACE) : t : lay pos cs ts

-- If we're in a layout context and the new token is not on the 
-- same line as the previous, we check the column against the
-- context. If the new token is on the same line, we only need
-- to check whether a context has to be added.
lay     prev@(Pos prevLine prevCol) 
        cc@(CtxLay ctxCol _:cs) 
        input@(t@(pos@(Pos line col), _):ts) 
    | line > prevLine = -- token on next line?
        if col > ctxCol then -- indent more => nothing
            t : addContext pos cc input
        else if col == ctxCol then -- indent same => insert ';' 
            (pos, LexINSERTED_SEMI) : t : addContext pos cc input
        else -- indent less => insert brace, remove context and try again
            (pos, LexINSERTED_RBRACE) : lay prev cs input
    | otherwise = -- token on same line
        t : addContext pos cc input

lay _ _ [] = []

lay     prev 
        [] 
        input@(t@(pos, _):_) = 
    t : addContext pos [] input

addContext :: Pos -> [Context] -> [Token] -> [Token]

-- If we see a '{' we add a CtxBrace context
addContext prev cs (t@(pos, LexSpecial '{'):ts) = 
    lay prev (CtxBrace : cs) ts

-- If we see a 'do', 'where', 'of' or 'let' we add a context
-- and a '{' only if the next token is not a '{'
addContext prev cs 
        (t@(pos, LexKeyword keyword):t2@(pos2@(Pos line2 col2), lexeme2):ts) 
    | keyword `elem` ["do", "where", "of","let"] =
        if lexeme2 == LexSpecial '{' then
            lay prev cs (t2:ts)
        else
            (pos2, LexINSERTED_LBRACE) :
            lay prev (CtxLay col2 (keyword == "let") : cs) (t2:ts)
    | otherwise = 
        lay prev cs (t2:ts)

addContext prev cs (_:ts) =
    lay prev cs ts

addContext _ _ [] = []

-----------------------------------------------------------
-- Lexer
-----------------------------------------------------------

data Pos        = Pos !Int !Int
instance Show Pos where
   show (Pos l c) = show (l, c)
   
type Token      = (Pos,Lexeme)

data Lexeme     = LexUnknown         Char
                | LexError           String
                | LexChar            String
                | LexString          String
                | LexInt             String
                | LexFloat           String
                | LexVar             String
                | LexVarSym          String
                | LexCon             String
                | LexConSym          String
                
                | LexKeyword         String
                | LexResVarSym       String
                | LexResConSym       String
                | LexSpecial         Char

                | LexINSERTED_LBRACE -- { inserted because of layout
                | LexINSERTED_RBRACE -- }
                | LexINSERTED_SEMI   -- ;
                
                | LexEOF
                deriving Eq

instance Show Lexeme where
    show x = case x of
        LexUnknown t        -> "unknown token"          ++ " '" ++ t       : "'"
        
        LexError   e        -> e
        LexChar    c        -> "character literal"      ++ " '" ++ c      ++ "'"
        LexString  s        -> "string literal"         ++ " \""++ s      ++ "\""
        LexInt     i        -> "integer literal"        ++ " '" ++ i      ++ "'"
        LexFloat   f        -> "floating-point literal" ++ " '" ++ f      ++ "'"
        LexVar     n        -> "variable"               ++ " '" ++ n      ++ "'"
        LexVarSym  o        -> "operator"               ++ " '" ++ o      ++ "'"
        LexCon     c        -> "constructor"            ++ " '" ++ c      ++ "'"
        LexConSym  o        -> "constructor operator"   ++ " '" ++ o      ++ "'"
        
        LexKeyword kwd      -> "keyword '" ++ kwd ++ "'"
        LexResVarSym s      -> "'" ++ s ++ "'"
        LexResConSym s      -> "'" ++ s ++ "'"
        LexSpecial c        -> "'" ++ [c] ++ "'"
        
        LexINSERTED_LBRACE  -> "inserted '{'"
        LexINSERTED_RBRACE  -> "end of block (based on layout)"
        LexINSERTED_SEMI    -> "next in block (based on layout)"
                        
        LexEOF              -> "end of file"
        
        _                   -> "unknown"

lexemeLength :: Lexeme -> Int
lexemeLength l = case l of
    LexUnknown         _     -> 1
    LexSpecial         _     -> 1
    LexChar            s     -> length s + 2 -- count the quotes, too
    LexString          s     -> length s + 2
    LexInt             s     -> length s
    LexFloat           s     -> length s
    LexVar             s     -> length s
    LexVarSym          s     -> length s
    LexCon             s     -> length s
    LexConSym          s     -> length s
    LexKeyword         s     -> length s
    LexResVarSym       s     -> length s
    LexResConSym       s     -> length s
    _                        -> 0
    
lexer :: Pos -> [Char] -> [Token]
lexer (Pos ln col) []           = [((Pos (ln+1) 0), LexEOF)]

lexer pos ('-':'-':cs)          = nextinc lexeol pos 2 cs
lexer pos ('{':'-':cs)          = nextinc (lexComment [pos] 0) pos 2 cs

lexer pos input@('\'':cs)       = lexChar   pos input
lexer pos input@('"':cs)        = lexString pos input

lexer pos input@(c:cs) 
    | isLower c || c == '_' = -- variable or keyword
        lexALot pos input isLetter LexVar LexKeyword keywords
    | isSpace c =
        next lexer pos c cs        
    | isUpper c = -- constructor
        lexCon          pos input
    | c == ':' = -- constructor operator
        lexALot pos input isSymbol LexConSym LexResConSym reservedConSyms
    | isSymbol c = -- variable operator
        lexALot pos input isSymbol LexVarSym LexResVarSym reservedVarSyms
    | c `elem` specials = 
        (pos, LexSpecial c) : nextinc lexer pos 1 cs
    | isDigit c = -- number
        lexIntFloat pos input
    | otherwise =
        (pos, LexUnknown c) : nextinc lexer pos 1 cs
    
lexALot pos cs predicate normal reserved reserveds =
    let (name, rest) = span predicate cs
        token = if name `elem` reserveds
                then reserved name 
                else normal   name
    in (pos, token) : nextinc lexer pos (length name) rest

keywords = 
    [ "let", "in", "do", "where", "case", "of", "if"
    , "then", "else", "data", "type", "module", "import"
    , "infix", "infixl", "infixr", "_"
    , "class", "instance", "default", "deriving", "newtype" -- not supported
    , "phase", "constraints" -- Bastiaan
    ]

reservedConSyms =
    [ "::"
    , ":" -- Bastiaan
    ]

reservedVarSyms =
    [ "=>", "->", "<-", "..", "-", "-.", "@", "=", "\\", "|"
    , "==" -- Bastiaan
    ]

specials = 
    ",`;{}()[]" 
    
lexCon pos cs = 
    let (name, rest) = span isLetter cs
    in (pos, LexCon name) : nextinc lexer pos (length name) rest

next f pos c cs                 = let pos' = newpos pos c  in seq pos' (f pos' cs)
nextinc f pos i cs              = let pos' = incpos pos i  in seq pos' (f pos' cs)

foldl' f x []                   = x
foldl' f x (y:ys)               = let z = f x y  in seq z (foldl' f z ys)

-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------

lexIntFloat pos input = 
    let (digits, rest) = span isDigit input
        posBehindDigits = incpos pos (length digits)
    in case rest of
        ('.':rest2@(next:_)) | isDigit next ->
            let (fraction, rest3) = span isDigit rest2
                posBehindFraction = incpos posBehindDigits (length fraction + 1)
                prefix = digits ++ "." ++ fraction
            in lexMaybeExponent pos prefix LexFloat rest3
        _ ->
            lexMaybeExponent pos digits LexInt rest

lexMaybeExponent pos prefix token input = 
    case input of
        ('e':'+':rest) ->
            lexExponent pos (prefix ++ "e+") rest
        ('E':'+':rest) ->
            lexExponent pos (prefix ++ "E+") rest
        ('e':'-':rest) ->
            lexExponent pos (prefix ++ "e-") rest
        ('E':'-':rest) ->
            lexExponent pos (prefix ++ "E-") rest
        ('e':rest) ->
            lexExponent pos (prefix ++ "e") rest
        ('E':rest) ->
            lexExponent pos (prefix ++ "E") rest
        _ ->
            (pos, token prefix) :
            lexer posBehindPrefix input
    where
        posBehindPrefix = incpos pos (length prefix)

lexExponent startPos prefix input =
    let (exponent, rest) = span isDigit input
        posAtExponent = incpos startPos (length prefix)
        posBehindExponent = incpos posAtExponent (length exponent)
    in if null exponent then
            (posAtExponent, LexError missingExponentDigits) : 
            lexer posAtExponent input
       else
            (startPos, LexFloat (prefix ++ exponent)) :
            lexer posBehindExponent rest

-----------------------------------------------------------
-- Characters
-----------------------------------------------------------

lexChar pos ('\'':'\\':c:'\'':cs) = 
    if c `elem` escapeChars then    
        (pos, LexChar ['\\',c]) : lexer (incpos pos 4) cs
    else
        (pos, LexError illegalEscapeInChar) : lexer (incpos pos 4) cs
lexChar pos ('\'':'\'':cs) = 
    (pos, LexError emptyChar) : 
    lexer (incpos pos 2) cs
lexChar pos ('\'':c:'\'':cs) =
    if ord c >= 32 && ord c <= 126 then 
        (pos, LexChar [c]) : lexer (incpos pos 3) cs
    else
        (pos, LexError illegalCharInChar) : lexer (incpos pos 3) cs
lexChar pos ('\'':c:cs) =
    (pos, LexError nonTerminatedChar) : lexer (incpos pos 2) cs
lexChar pos ['\''] = 
    (pos, LexError eofInChar) : lexer pos []

lexString startPos ('"':cs) = lexStringChar (incpos startPos 1) cs ""
  where
    lexStringChar pos [] s = 
        (pos, LexError eofInString) : lexer pos []
    lexStringChar pos ('\\':c:cs) s =
        if c `elem` escapeChars then
            lexStringChar (incpos pos 2) cs (c:'\\':s)
        else
            (pos, LexError illegalEscapeInString) : 
            lexStringChar (incpos pos 2) cs s
    lexStringChar pos ('"':cs) s =
        (startPos, LexString (reverse s)) : lexer (incpos pos 1) cs
    lexStringChar pos ('\n':cs) s =
        (pos, LexError newlineInString) : 
        lexer (newpos pos '\n') cs
    lexStringChar pos (c:cs) s =
        if ord c >= 32 && ord c <= 126 then
            lexStringChar (incpos pos 1) cs (c:s)
        else
            (pos, LexError illegalCharInString) : 
            lexStringChar (incpos pos 1) cs s
        
-----------------------------------------------------------
-- Symbols
-----------------------------------------------------------

isSymbol c                      = elem c "!#$%&*+./<=>?@^|-~:\\"
                                  
isLetter '\''                   = True
isLetter '_'                    = True
isLetter c                      = isAlphaNum c

escapeChars = "\\nabfnrtv\"'"
                                  
-----------------------------------------------------------
-- Comment
-----------------------------------------------------------

lexeol :: Pos -> String -> [Token]
lexeol pos ('\n':cs)    = next lexer pos '\n' cs
lexeol pos (c:cs)       = next lexeol pos c cs
lexeol pos []           = lexer pos []

lexComment :: [Pos] -> Int -> Pos -> String -> [Token]
lexComment starts level pos ('-':'}':cs)   
    | level == 0    = nextinc lexer pos 2 cs
    | otherwise     = nextinc (lexComment (tail starts) (level - 1)) pos 2 cs
lexComment starts level pos ('{':'-':cs) = 
    nextinc (lexComment (pos:starts) (level+1)) pos 2 cs
lexComment starts level pos (c:cs) = 
    next (lexComment starts level) pos c cs
lexComment starts level pos [] 
    = (head starts, LexError unterminatedComment) : lexer pos []
-- at end-of-file show the most recently opened comment

-----------------------------------------------------------
-- Positions
-----------------------------------------------------------

incpos (Pos line col) i     = Pos line (col+i)

newpos (Pos line col) '\n'  = Pos (line + 1) 1
newpos (Pos line col) '\t'  = Pos line (((((col-1) `div` 8)+1)*8)+1)
newpos (Pos line col) c     = Pos line (col+1)

nonTerminatedChar     = "non-terminated character literal"
illegalCharInChar     = "illegal character in character literal"
emptyChar             = "empty character literal"
eofInChar             = "end-of-file in character literal"
illegalEscapeInChar   = "illegal escape sequence in character literal"

newlineInString       = "newline in string literal (expecting \")"
illegalCharInString   = "illegal character in string literal"
eofInString           = "end-of-file in string literal"
illegalEscapeInString = "illegal escape sequence in string literal"

missingExponentDigits = "missing digits in exponent"

unterminatedComment   = "unterminated comment"

charErrors    = [ nonTerminatedChar, illegalCharInChar, emptyChar, eofInChar ]
stringErrors  = [ newlineInString, illegalCharInString, eofInString ]
floatErrors   = [ missingExponentDigits ]
commentErrors = [ unterminatedComment ]