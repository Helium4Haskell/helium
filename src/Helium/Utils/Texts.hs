module Helium.Utils.Texts where

import Data.IORef
import System.IO.Unsafe

data Language = English | Dutch deriving Eq

language :: IORef Language
language = unsafePerformIO (newIORef English)

data Arrow a b = a :-> b

infix 0 :->

select :: IORef Language -> [Arrow Language msg] -> msg
select languageRef table = 
    let currentLanguage = unsafePerformIO (readIORef languageRef)
        convert (a :-> b) = (a, b)
    in case lookup currentLanguage (map convert table) of
        Nothing -> error "Texts.select: unknown language"
        Just msg -> msg

warning :: String
warning = select language
    [ English :-> "Warning"
    , Dutch   :-> "Waarschuwing"
    ]

hint :: String    
hint = select language
    [ English :-> "Hint"
    , Dutch   :-> "Hint"
    ]

parserSyntaxError :: String
parserSyntaxError = select language
    [ English :-> "Syntax error"
    , Dutch   :-> "Syntax fout"
    ]
    
parserOr :: String    
parserOr = select language 
    [ English :-> "or"
    , Dutch   :-> "of"
    ]

parserUnknown :: String
parserUnknown = select language
    [ English :-> "unknown parse error" 
    , Dutch   :-> "onbekende syntax fout"
    ]

parserExpecting :: String
parserExpecting = select language
    [ English :-> "expecting"
    , Dutch   :-> "verwacht: "
    ]

parserUnexpected :: String
parserUnexpected = select language
    [ English :-> "unexpected"
    , Dutch   :-> "onverwacht: "
    ]

parserEndOfInput :: String 
parserEndOfInput = select language
    [ English :-> "end of input"
    , Dutch   :-> "einde van de tekst"
    ]

parserSingleDigitPriority :: String
parserSingleDigitPriority = select language
    [ English :-> "priority must be a single digit"
    , Dutch   :-> "de prioriteit mag maar uit 1 cijfer bestaan"
    ]
    
parserTypeClass :: String
parserTypeClass = select language
    [ English :-> "type class"
    , Dutch   :-> "type klasse"
    ]

parserTypeConstructor :: String
parserTypeConstructor = select language
    [ English :-> "type constructor"
    , Dutch   :-> "type constructor"
    ]

parserTypeVariable :: String
parserTypeVariable = select language
    [ English :-> "type variable"
    , Dutch   :-> "type variabele"
    ]

parserModuleName :: String
parserModuleName = select language
    [ English :-> "module name"
    , Dutch   :-> "module naam"
    ]

parserVariable :: String
parserVariable = select language
    [ English :-> "variable"
    , Dutch   :-> "variabele"
    ]

parserConstructor :: String
parserConstructor = select language
    [ English :-> "constructor"
    , Dutch   :-> "constructor"
    ]

parserConstructorOperator :: String
parserConstructorOperator = select language
    [ English :-> "constructor operator"
    , Dutch   :-> "constructor operator"
    ]

parserOperator :: String
parserOperator = select language
    [ English :-> "operator"
    , Dutch   :-> "operator"
    ]

parserCharacterLiteral :: String
parserCharacterLiteral = select language
    [ English :-> "character literal"
    , Dutch   :-> "letter constante"
    ]

parserStringLiteral :: String
parserStringLiteral = select language
    [ English :-> "string literal"
    , Dutch   :-> "string constante"
    ]
    
parserIntegerLiteral :: String
parserIntegerLiteral = select language
    [ English :-> "integer literal"
    , Dutch   :-> "geheel getal"
    ]

parserFloatLiteral :: String
parserFloatLiteral = select language
    [ English :-> "floating-point literal"
    , Dutch   :-> "reeel getal"
    ]

parserKeyword :: String
parserKeyword = select language
    [ English :-> "keyword"
    , Dutch   :-> "gereserveerd woord"
    ]

parserInsertedLBrace :: String
parserInsertedLBrace = select language
    [ English :-> "inserted '{'"
    , Dutch   :-> "ingevoegde '{'"
    ]

parserEndOfFile :: String
parserEndOfFile = select language
    [ English :-> "end of file"
    , Dutch   :-> "einde van het bestand"
    ]

parserNextInBlock :: String
parserNextInBlock = select language
    [ English :-> "next in block (based on layout)"
    , Dutch   :-> "volgende in blok (d.m.v. inspringing)"
    ]

parserEndOfBlock :: String
parserEndOfBlock = select language
    [ English :-> "end of block (based on layout)"
    , Dutch   :-> "einde van het blok (d.m.v. inspringing)"
    ]

parserExpression :: String
parserExpression = select language
    [ English :-> "expression"
    , Dutch   :-> "expressie"
    ]

parserPattern :: String
parserPattern = select language
    [ English :-> "pattern"
    , Dutch   :-> "patroon"
    ]

parserType :: String
parserType = select language
    [ English :-> "type"
    , Dutch   :-> "type"
    ]

parserLiteral :: String
parserLiteral = select language
    [ English :-> "literal"
    , Dutch   :-> "constante"
    ]

parserNumericLiteral :: String
parserNumericLiteral = select language
    [ English :-> "numeric literal"
    , Dutch   :-> "getal"
    ]

parserImportDeclaration :: String
parserImportDeclaration = select language
    [ English :-> "import declaration"
    , Dutch   :-> "import declaratie"
    ]

parserDeclaration :: String
parserDeclaration = select language
    [ English :-> "declaration"
    , Dutch   :-> "declaratie"
    ]

lexerUnterminatedComment :: String
lexerUnterminatedComment = select language
    [ English :-> "Unterminated comment"
    , Dutch   :-> "Commentaar niet afgesloten"
    ]

lexerMissingExponentDigits :: String
lexerMissingExponentDigits = select language
    [ English :-> "Missing digits in exponent in floating-point literal"
    , Dutch   :-> "Geen cijfers in de exponent van een reeel getal"
    ]

lexerUnexpectedChar :: Char -> String
lexerUnexpectedChar c = select language
    [ English :-> "Unexpected character '" ++ [c] ++ "'"
    , Dutch   :-> "Onverwachte letter '" ++ [c] ++ "'"
    ]

lexerIllegalEscapeInChar :: String
lexerIllegalEscapeInChar = select language
    [ English :-> "Illegal escape sequence in character literal" 
    , Dutch   :-> "Illegaal escape karakter in letter constante"
    ]

lexerEmptyChar :: String
lexerEmptyChar = select language
    [ English :-> "Empty character literal" 
    , Dutch   :-> "Lege letter constante"
    ]

lexerIllegalCharInChar :: String
lexerIllegalCharInChar = select language
    [ English :-> "Illegal character in character literal" 
    , Dutch   :-> "Niet toegestaan teken in letter constante"
    ]

lexerNonTerminatedChar :: String
lexerNonTerminatedChar = select language
    [ English :-> "Non-terminated character literal"
    , Dutch   :-> "Niet afgesloten letter constante"
    ]

lexerInfixHint :: String -> String
lexerInfixHint name = select language
    [ English :-> "To write a function in infix notation, use backquotes: `" ++ name ++ "`"
    , Dutch   :-> "Om een functie infix te schrijven gebruik je backquotes: `" ++ name ++ "`"
    ]

lexerEOFInChar :: String
lexerEOFInChar = select language
    [ English :-> "End of file in character literal"
    , Dutch   :-> "Einde van bestand in letter constante"
    ]

lexerEOFInString :: String
lexerEOFInString = select language
    [ English :-> "End of file in string literal"
    , Dutch   :-> "Einde van bestand in tekst constante"
    ]

lexerIllegalEscapeInString :: String
lexerIllegalEscapeInString = select language 
    [ English :-> "Illegal escape sequence in string literal"
    , Dutch   :-> "Illegaal escape karakter in tekst constante"
    ]
    
lexerNewLineInString :: String
lexerNewLineInString = select language 
    [ English :-> "Newline in string literal (expecting \")"
    , Dutch   :-> "Einde van regel in een tekst (gebruik \" om de tekst te sluiten)"
    ]

lexerIllegalCharInString :: String
lexerIllegalCharInString = select language 
    [ English :-> "Illegal character in string literal"
    , Dutch   :-> "Niet toegestaan teken in tekst constante"
    ]

lexerTooManyClose :: Show a => a -> String
lexerTooManyClose c = select language 
    [ English :-> "Close bracket " ++ show c ++ " but no open bracket"
    , Dutch   :-> "Haakje " ++ show c ++ " wordt gesloten maar nergens geopend"
    ]

lexerUnexpectedClose :: (Show a, Show b) => a -> b -> [String]
lexerUnexpectedClose c1 c2 = select language 
    [ English :-> [ "Unexpected close bracket " ++ show c1
                  , "Expecting a close bracket for " ++ show c2
                  ]
    , Dutch   :-> [ "Onverwacht sluithaakje " ++ show c1
                  , "Sluithaakje voor " ++ show c2 ++ " wordt nog verwacht"
                  ]
    ]

lexerStillOpenAtEOF :: [String] -> String
lexerStillOpenAtEOF [s] = select language 
    [ English :-> "Bracket " ++ s ++ " is never closed"
    , Dutch   :-> "Sluithaakje voor " ++ s ++ " wordt nog verwacht"
    ]
lexerStillOpenAtEOF xs = select language 
    [ English :-> "The following brackets are never closed: " ++ commasAnd xs
    , Dutch   :-> "De volgende haakjes worden nergens gesloten: " ++ kommasEn xs
    ]

lexerCorrectFloats :: String
lexerCorrectFloats = select language 
    [ English :-> "Correct examples of Floats: 3.14 0.2 4e-13 5E+1 6.7e1"
    , Dutch   :-> "Correcte voorbeelden van reeele getallen: 3.14 0.2 4e-13 5E+1 6.7e1"
    ]

lexerCorrectChars :: String
lexerCorrectChars = select language 
    [ English :-> "Correct examples of Chars: 'a' '\\n' '&'"   
    , Dutch   :-> "Correcte voorbeelden van letters: 'a' '\\n' '&'"   
    ]

lexerCorrectStrings :: String
lexerCorrectStrings = select language 
    [ English :-> "Correct examples of Strings: \"Helium is cool\" \"abc\\ndef\" \"\"" 
    , Dutch   :-> "Correcte voorbeelden van teksten: \"Helium is geweldig\" \"abc\\ndef\" \"\""
    ]
 
lexerTabCharacter :: [String]
lexerTabCharacter = select language 
    [ English :-> [ "Tab character encountered; may cause problems with the layout rule"
                  , "Configure your editor to replace tabs by spaces" 
                  ]
    , Dutch   :-> [ "Tab karakters kunnen problemn opleveren met de layout rule"
                  , "Stel je editor zo in dat hij tabs vervangt door spaties"
                  ]
    ]

lexerLooksLikeFloatNoFraction :: String -> [String]
lexerLooksLikeFloatNoFraction digits = select language 
    [ English :-> [ "Integer immediately followed by function composition (.)"
                  , "If a Float was meant, write \"" ++ digits ++ ".0\""
                  , "Otherwise, insert a space for readability" 
                  ]
    , Dutch   :-> [ "Geheel getal direct gevolgd door functie compositie (.)"
                  , "Als je een reeel getal bedoelde, schrijf dan \"" ++ digits ++ ".0\""
                  , "Voeg anders een spatie in voor leesbaarheid"
                  ]
    ]

lexerLooksLikeFloatNoDigits :: String -> [String]
lexerLooksLikeFloatNoDigits fraction = select language 
    [ English :-> [ "Function composition (.) immediately followed by number"
                  , "If a Float was meant, write \"0." ++ fraction ++ "\""
                  , "Otherwise, insert a space for readability" 
                  ]
    , Dutch   :-> [ "Functie compositie (.) direct gevolgd door een getal"
                  , "Als je een reeel getal bedoelde, schrijf dan \"0." ++ fraction ++ "\""
                  , "Voeg anders een spatie in voor leesbaarheid"
                  ]
    ]            

lexerNestedComment :: [String]
lexerNestedComment = select language 
    [ English :-> [ "Syntax colouring usually can not handle nested comments"
                  , "Some of your code may be in comments but not visibly so"
                  ]
    , Dutch   :-> [ "Syntax kleuring van editor kan meestal niet overweg met genest commentaar"
                  , "Het kan zo zijn dat een deel van je code in commentaar staat maar dat je dat niet ziet"
                  ]
    ]            
            
lexerCommentOperator :: [String]
lexerCommentOperator = select language 
    [ English :-> [ "Syntax colouring usually can not handle names containing --" 
                  , "If you wanted to start a comment, write spaces around --"
                  ]
    , Dutch   :-> [ "Syntax kleuring van editor kan meestal niet overweg met namen die -- bevatten"
                  , "Als je commentaar wilde beginnen schrijf dan spaties voor en na --"
                  ]
    ]


commasAnd :: [String] -> String
commasAnd [] = []
commasAnd [x] = x
commasAnd (x:xs) = x ++ concatMap (", " ++) (init xs) ++ " and " ++ last xs

kommasEn :: [String] -> String
kommasEn [] = []
kommasEn [x] = x
kommasEn (x:xs) = x ++ concatMap (", " ++) (init xs) ++ " en " ++ last xs

