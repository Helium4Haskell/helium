module LexerMessage
    ( LexerError(..)
    , LexerErrorInfo(..)
    , LexerWarning(..)
    , LexerWarningInfo(..)
    , keepOneTabWarning
    ) where

import Text.ParserCombinators.Parsec.Pos
import UHA_Syntax(Range(..), Position(..))
import Messages

instance HasMessage LexerError where
    getRanges (LexerError _ (StillOpenAtEOF brackets)) =
        reverse (map (sourcePosToRange . fst) brackets)
    getRanges (LexerError pos (UnexpectedClose _ pos2 _)) =
        map sourcePosToRange [pos, pos2]
    getRanges (LexerError pos _) =
        [ sourcePosToRange pos ]
    getMessage (LexerError _ info) = 
        let (line:rest) = showLexerErrorInfo info
        in MessageOneLiner (MessageString line) :
            [ MessageHints "Hint" [ MessageString s | s <- rest ] ]

sourcePosToRange :: SourcePos -> Range
sourcePosToRange pos = 
    let name = sourceName pos; line = sourceLine pos; col = sourceColumn pos
        position = Position_Position name line col
    in Range_Range position position
    
data LexerError =
    LexerError SourcePos LexerErrorInfo
    
data LexerErrorInfo
    = UnterminatedComment
    | MissingExponentDigits
    | UnexpectedChar Char

    | IllegalEscapeInChar
    | EmptyChar
    | IllegalCharInChar
    | NonTerminatedChar (Maybe String)
    | EOFInChar

    | EOFInString
    | IllegalEscapeInString
    | NewLineInString
    | IllegalCharInString

    | TooManyClose Char
        -- In UnexpectedClose, first char is the closing bracket we see, 
        -- second char is the closing bracket we would like to see first
        -- e.g. [(1,3]  =>  UnexpectedClose ']' ... ')'
    | UnexpectedClose Char SourcePos Char
    | StillOpenAtEOF [(SourcePos, Char)]

showLexerErrorInfo :: LexerErrorInfo -> [String]
showLexerErrorInfo info =
    case info of
        UnterminatedComment -> ["Unterminated comment"]
        MissingExponentDigits -> [ "Missing digits in exponent in floating-point literal"
                                 , correctFloats 
                                 ]
        UnexpectedChar c -> ["Unexpected character '" ++ [c] ++ "'"]
        
        IllegalEscapeInChar -> [ "Illegal escape sequence in character literal", correctChars ]
        EmptyChar -> [ "Empty character literal", correctChars ]
        IllegalCharInChar -> [ "Illegal character in character literal", correctChars ]
        NonTerminatedChar mn -> 
            [ "Non-terminated character literal"
            , correctChars
            ] ++ case mn of
                   Nothing -> []
                   Just name -> ["To write a function in infix notation, use backquotes: `" ++ name ++ "`" ]
        EOFInChar -> [ "End of file in character literal", correctChars]
        
        EOFInString -> ["End of file in string literal", correctStrings ]
        IllegalEscapeInString -> ["Illegal escape sequence in string literal", correctStrings ]
        NewLineInString -> ["Newline in string literal (expecting \")", correctStrings ]
        IllegalCharInString -> ["Illegal character in string literal", correctStrings]
                
        TooManyClose c -> ["Close bracket " ++ show c ++ " but no open bracket"]
        UnexpectedClose c1 _ c2 -> 
            [ "Unexpected close bracket " ++ show c1
            , "Expecting a close bracket for " ++ show c2 
            ]
        StillOpenAtEOF [b] -> ["Bracket " ++ show (snd b) ++ " is never closed"]
        StillOpenAtEOF bs -> ["The following brackets are never closed: " ++
            commasAnd (reverse (map (show.snd) bs)) ]
            -- 'reverse' because positions will be sorted and brackets are
            -- reported in reversed order

correctFloats, correctChars, correctStrings :: String
correctFloats  = "Correct examples of Floats: 3.14 0.2 4e-13 5E+1 6.7e1"
correctChars   = "Correct examples of Chars: 'a' '\\n' '&'"
correctStrings = "Correct examples of Strings: \"Helium is cool\" \"abc\\ndef\" \"\""

commasAnd :: [String] -> String
commasAnd [] = []
commasAnd [x] = x
commasAnd (x:xs) = x ++ concatMap (", " ++) (init xs) ++ " and " ++ last xs

instance HasMessage LexerWarning where
    getRanges (LexerWarning pos (NestedComment pos2)) =
       map sourcePosToRange [ pos, pos2 ]
    getRanges (LexerWarning pos _) =
        [ sourcePosToRange pos ]
    getMessage (LexerWarning _ info) = 
        let (line:rest) = showLexerWarningInfo info
        in MessageOneLiner (MessageString ("Warning: " ++ line)) :
            [ MessageHints "Hint" [ MessageString s | s <- rest ] ]

data LexerWarning =
    LexerWarning SourcePos LexerWarningInfo

data LexerWarningInfo 
    = TabCharacter
    | LooksLikeFloatNoFraction String
    | LooksLikeFloatNoDigits String
    | NestedComment SourcePos
    | CommentOperator

showLexerWarningInfo :: LexerWarningInfo -> [String]
showLexerWarningInfo info = 
    case info of
        TabCharacter -> 
            [ "Tab character encountered; may cause problems with the layout rule"
            , "Configure your editor to replace tabs by spaces" 
            ]
        LooksLikeFloatNoFraction digits ->
            [ "Integer immediately followed by function composition (.)"
            , "If a Float was meant, write \"" ++ digits ++ ".0\""
            , "Otherwise, insert a space for readability" 
            ]
        LooksLikeFloatNoDigits fraction ->
            [ "Function composition (.) immediately followed by number"
            , "If a Float was meant, write \"0." ++ fraction ++ "\""
            , "Otherwise, insert a space for readability" 
            ]

        NestedComment _ ->
            [ "Syntax colouring usually can not handle nested comments"
            , "Some of your code may be in comments but not visibly so"
            ]
        
        CommentOperator ->
            [ "Syntax colouring usually can not handle names containing --" 
            , "If you wanted to start a comment, write spaces around --"
            ]
            
keepOneTabWarning :: [LexerWarning] -> [LexerWarning]
keepOneTabWarning = keepOneTab True
  where
    keepOneTab isFirst (warning@(LexerWarning _ TabCharacter):rest)
        | isFirst   = warning : keepOneTab False rest
        | otherwise = keepOneTab isFirst rest
    keepOneTab isFirst (warning:rest) = 
        warning : keepOneTab isFirst rest
    keepOneTab _ [] = []
