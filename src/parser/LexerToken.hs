module LexerToken where

import ParsecPos(SourcePos)

type Token      = (SourcePos,Lexeme)

data Lexeme     
    = LexChar            String
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

    | LexInsertedOpenBrace  -- { inserted because of layout
    | LexInsertedCloseBrace -- }
    | LexInsertedSemicolon  -- ;

    | LexEOF
    deriving Eq

instance Show Lexeme where
    show x = case x of
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
        
        LexInsertedOpenBrace  -> "inserted '{'"
        LexInsertedCloseBrace -> "end of block (based on layout)"
        LexInsertedSemicolon  -> "next in block (based on layout)"
                        
        LexEOF              -> "end of file"
        
lexemeLength :: Lexeme -> Int
lexemeLength l = case l of
    LexChar            s     -> length s + 2 -- count the quotes, too
    LexString          s     -> length s + 2
    LexInt             s     -> length s
    LexFloat           s     -> length s

    LexVar             s     -> length s
    LexVarSym          s     -> length s
    LexCon             s     -> length s
    LexConSym          s     -> length s

    LexSpecial         _     -> 1
    LexKeyword         s     -> length s
    LexResVarSym       s     -> length s
    LexResConSym       s     -> length s
    _                        -> 0
