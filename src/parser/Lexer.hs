module Lexer -- 568 regels
    ( Token, Lexeme(..), Pos
    , lexer
    , layout, addLayout
    , incpos, lexemeLength
    ) where

import Char

-----------------------------------------------------------
-- The layout rule
-----------------------------------------------------------

layout :: [Token] -> [Token]
layout  = lay [] . addLayout


data Context   = CtxLay Int
               | CtxLet Int
               | CtxBrace
               deriving (Eq,Show)


lay :: [Context] -> [Token] -> [Token]


lay (CtxLet c:cs) ((_,Indent i):t@(pos,LexKeyword "in"):ts)   = (pos,LexINSERTED_RBRACE) : t : lay cs ts
lay (CtxLet c:cs) (t@(pos,LexKeyword "in"):ts)        = (pos,LexINSERTED_RBRACE) : t : lay cs ts

lay cc@(CtxBrace:cs) ((pos,Indent i):ts)    = lay cc ts

{-
lay cc@(CtxLet c:cs) tt@(t@(_,LexSEMI):(pos,Indent i):ts)   
                                            = t : lay cc ts
-}                                            
lay cc@(CtxLet c:cs) tt@((pos,Indent i):ts) | i == c    = (pos,LexINSERTED_SEMI) : lay cc ts
                                            | i  < c    = (pos,LexINSERTED_RBRACE) : lay cs tt
                                            | otherwise = lay cc ts
{-
lay cc@(CtxLay c:cs) tt@(t@(_,LexSEMI):(pos,Indent i):ts)   
                                            | i == c    = t : lay cc ts
                                            | i  < c    = (pos,LexRBRACE) : lay cs tt
                                            | otherwise = lay cc ts
-}
lay cc@(CtxLay c:cs) tt@((pos,Indent i):ts) | i == c    = (pos,LexINSERTED_SEMI) : lay cc ts
                                            | i  < c    = (pos,LexINSERTED_RBRACE) : lay cs tt
                                            | otherwise = lay cc ts
                                            
lay cs (t@(pos,LexSpecial '{'):ts)               = t : lay (CtxBrace:cs) ts
lay (CtxBrace:cs) (t@(pos,LexSpecial '}'):ts)    = t : lay cs ts

lay cs ((pos,Indent i):ts)                  = lay cs ts
lay cs ((pos,Layout c):ts)                  = (pos,LexINSERTED_LBRACE) : lay (c:cs) ts

lay cs (t:ts)                               = t : lay cs ts
lay cs []                                   = []


addLayout tt@((pos,LexKeyword "module"):ts)   = addLay pos tt 
addLayout tt@((pos,LexSpecial '{'):ts)   = addLay pos tt
addLayout tt@((pos,_):ts)           = (pos,Layout (CtxLay (snd pos))) : addLay pos tt
addLayout []                        = []

addLay :: Pos -> [Token] -> [Token]
addLay pos []                           = []
--addLay _ (t@(pos,LexIN):ts)             = t : addLay pos ts
addLay (l,c) (t@(pos,lexeme):ts)   
            | ln > l     = (pos,Indent col) : t : rest
            | otherwise  = t : rest
            where
              (ln,col)   = pos
              rest       = case lexeme of 
                                     LexKeyword "let"   -> newlay CtxLet
                                     LexKeyword "where" -> newlay CtxLay
                                     LexKeyword "of"    -> newlay CtxLay
                                     LexKeyword "do"    -> newlay CtxLay
                                     _         -> addLay pos ts
                                                          
              newlay ctx = case ts of
                             [] -> []
                             (u@(pos',LexSpecial '{'):us) 
                                -> u : addLay pos' us
                             (u@(pos',lexeme'):us)   
                                -> (pos',Layout (ctx (snd pos'))) : u : addLay pos' us
                      
                      
                      
-----------------------------------------------------------
-- Lexer
-----------------------------------------------------------

type Pos        = (Int,Int)
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
                
                | Layout Context
                | Indent Int
                deriving Eq

instance Show Lexeme where
    show x = case x of
        LexUnknown t        -> "unknown token"          ++ " '" ++ t       : "'"
        
        LexError   e        -> e
        LexChar    c        -> "character literal"      ++ " '" ++ c      ++ "'"
        LexString  s        -> "string literal"         ++ " \""++ s      ++ "\""
        LexInt     i        -> "integer literal"        ++ " '" ++ show i ++ "'"
        LexFloat   f        -> "floating-point literal" ++ " '" ++ show f ++ "'"
        LexVar     n        -> "variable"               ++ " '" ++ n      ++ "'"
        LexVarSym  o        -> "operator"               ++ " '" ++ o      ++ "'"
        LexCon     c        -> "constructor"            ++ " '" ++ c      ++ "'"
        LexConSym  o        -> "constructor operator"   ++ " '" ++ o      ++ "'"
        
        LexKeyword kwd      -> "keyword '" ++ kwd ++ "'"
        LexResVarSym s      -> "'" ++ s ++ "'"
        LexResConSym s      -> "'" ++ s ++ "'"
        LexSpecial c        -> "'" ++ [c] ++ "'"
        
        LexINSERTED_LBRACE  -> "inserted '{'"
        LexINSERTED_RBRACE  -> "inserted '}'"
        LexINSERTED_SEMI    -> "inserted ;"
                        
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
    
lexer :: (Int, Int) -> [Char] -> [Token]
lexer (ln,col) []               = [((ln+1, 0), LexEOF)]

lexer pos ('-':'-':cs)          = nextinc lexeol pos 2 cs
lexer pos ('{':'-':cs)          = nextinc (lexComment 0) pos 2 cs

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
--- 1m24, 1m26 ./testSE
-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------

lexIntFloat pos input = 
    let (digits, rest) = span isDigit input
        posBehindDigits = incpos pos (length digits)
    in case rest of
        ('.':'.':rest2) -> -- think of "[0..]"
            (pos, LexInt digits) : lexer posBehindDigits rest
        ('.':rest2) ->
            let (fraction, rest3) = span isDigit rest2
                posBehindDot = incpos posBehindDigits 1
                posBehindFraction = incpos posBehindDot (length fraction)
            in if null fraction then 
                (posBehindDigits, LexError "'invalid fraction'") :
                lexer posBehindDot rest2
               else
                (pos, LexFloat (digits ++ "." ++ fraction)) :
                lexer posBehindFraction rest3 
        _ ->
            (pos, LexInt digits) : lexer posBehindDigits rest
           
-----------------------------------------------------------
-- Characters
-----------------------------------------------------------

lexChar pos ('\'':'\\':c:'\'':cs) = 
    if c `elem` escapeChars then    
        (pos, LexChar ['\\',c]) : lexer (incpos pos 4) cs
    else
        (pos, LexError "illegal escape sequence") : lexer (incpos pos 4) cs
lexChar pos ('\'':'\'':cs) = 
    (pos, LexError "empty character") : 
    lexer (incpos pos 2) cs
lexChar pos ('\'':c:'\'':cs) =
    if ord c >= 32 && ord c <= 126 then 
        (pos, LexChar [c]) : lexer (incpos pos 3) cs
    else
        (pos, LexError "illegal character") : lexer (incpos pos 3) cs
lexChar pos ('\'':c:cs) =
    (pos, LexError "unclosed character") : lexer (incpos pos 2) cs
lexChar pos ['\''] = 
    (pos, LexError "unexpected end of input in character") : lexer pos []

lexString startPos ('"':cs) = lexStringChar (incpos startPos 1) cs ""
  where
    lexStringChar pos [] s = 
        (pos, LexError "end of input in string") : lexer pos []
    lexStringChar pos ('\\':c:cs) s =
        if c `elem` escapeChars then
            lexStringChar (incpos pos 2) cs (c:'\\':s)
        else
            (pos, LexError "illegal escape sequence") : 
            lexStringChar (incpos pos 2) cs s
    lexStringChar pos ('"':cs) s =
        (startPos, LexString (reverse s)) : lexer (incpos pos 1) cs
    lexStringChar pos ('\n':cs) s =
        (pos, LexError "newline in string") : 
        lexer (newpos pos '\n') cs
    lexStringChar pos (c:cs) s =
        if ord c >= 32 && ord c <= 126 then
            lexStringChar (incpos pos 1) cs (c:s)
        else
            (pos, LexError "illegal character in string") : 
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

lexComment :: Int -> Pos -> String -> [Token]
lexComment level pos ('-':'}':cs)   
    | level == 0    = nextinc lexer pos 2 cs
    | otherwise     = nextinc (lexComment (level - 1)) pos 2 cs
lexComment level pos ('{':'-':cs) = 
    nextinc (lexComment (level+1)) pos 2 cs
lexComment level pos (c:cs) = 
    next (lexComment level) pos c cs
lexComment level pos [] 
    = lexer pos []

-----------------------------------------------------------
-- Positions
-----------------------------------------------------------

incpos (line,col) i           = (line,col+i)

newpos (line,col) '\n'  = (line + 1,1)
newpos (line,col) '\t'  = (line, ((((col-1) `div` 8)+1)*8)+1)
newpos (line,col) c     = (line, col+1)
