-----------------------------------------------------------
-- Daan Leijen (c) 2002
--
-- Haskell lexical syntax
-----------------------------------------------------------

-- Search for "AFIE" for diff

module HaskellLexer( HParser     -- a "Haskell" parser
                   , runHParser  -- takes care of start whitespace and eof

                   -- literals
                   , naturalOrFloat, float, natural 
                   , charLiteral, stringLiteral

                   -- identifiers and operators
                   , varid, conid, varsym, consym  
                   , qvarid, qconid, qvarsym, qconsym 
                   
                   -- reserved words, operators and specials
                   , reserved, reservedOp, special

                   , reservedIdNames, reservedOpNames, specialNames
                   
                   , getLastPosition -- AFIE
                   , layout -- AFIE
                   ) where

import List( sort )
import Parsec
import ParsecLayout
import ParsecPos -- AFIE
import Char -- AFIE, voor GHC

-----------------------------------------------------------
-- The Haskell Parser type: a layout parser on a character stream.
-----------------------------------------------------------
type HParser a  = LayoutParser Char SourcePos a

runHParser :: HParser a -> FilePath -> String -> Either ParseError a
runHParser p fname input
  = runLayoutParser (toplevel p) (newPos "" 0 0) fname input -- AFIE

-----------------------------------------------------------
-- Reserved identifiers and operators
-----------------------------------------------------------
symbol
  = oneOf "!#$%&*+./<=>?@\\^|-~"

reservedIdNames
  = sort ["case","class","data","default","deriving","do","else"
         ,"if","import","in","infix","infixl","infixr","instance"
         ,"let","module","newtype","of","then","type","where","_"]
                             
reservedOpNames
  = sort ["..","::","=","\\","|","<-","->","@","~","=>"]
    -- AFIE ":" niet meer gereserveerd
specialNames
  = ["(",")",",",";","[","]","`","{","}"
    ,"-","!"
    ]

-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------
naturalOrFloat :: HParser (Either Integer Double)
naturalOrFloat  = lexeme (natFloat) <?> "number"

float           = lexeme floating   <?> "float"
integer         = lexeme int        <?> "integer"
natural         = lexeme nat        <?> "natural"


-- floats
floating        = do{ n <- decimal 
                    ; fractExponent n
                    }


natFloat        = do{ char '0'
                    ; zeroNumFloat
                    }
                  <|> decimalFloat
                  
zeroNumFloat    =  do{ n <- hexadecimal <|> octal
                     ; return (Left n)
                     }
                <|> decimalFloat
                <|> fractFloat 0
                <|> return (Left 0)                  
                  
decimalFloat    = do{ n <- decimal
                    ; option (Left n) 
                             (fractFloat n)
                    }

fractFloat n    = do{ f <- fractExponent n
                    ; return (Right f)
                    }
                    
fractExponent n = do{ fract <- try fraction -- AFIE (list comprehension [1..6])
                    ; expo  <- option 1.0 exponent'
                    ; return ((fromInteger n + fract)*expo)
                    }
                <|>
                  do{ expo <- exponent'
                    ; return ((fromInteger n)*expo)
                    }

fraction        = do{ char '.'
                    ; digits <- many1 digit <?> "fraction"
                    ; return (foldr op 0.0 digits)
                    }
                  <?> "fraction"
                where
                  op d f    = (f + fromIntegral (digitToInt d))/10.0
                    
exponent'       = do{ oneOf "eE"
                    ; f <- sign
                    ; e <- decimal <?> "exponent"
                    ; return (power (f e))
                    }
                  <?> "exponent"
                where
                   power e  | e < 0      = 1.0/power(-e)
                            | otherwise  = fromInteger (10^e)


-- integers and naturals
int             = do{ f <- lexeme sign
                    ; n <- nat
                    ; return (f n)
                    }
                    
-- sign            :: CharParser st (Integer -> Integer)
sign            =   (char '-' >> return negate) 
                <|> (char '+' >> return id)     
                <|> return id

nat             = zeroNumber <|> decimal
    
zeroNumber      = do{ char '0'
                    ; hexadecimal <|> octal <|> decimal <|> return 0
                    }
                  <?> ""       

decimal         = number 10 digit        
hexadecimal     = do{ oneOf "xX"; number 16 hexDigit }
octal           = do{ oneOf "oO"; number 8 octDigit  }

number :: Integer -> HParser Char -> HParser Integer
number base baseDigit
    = do{ digits <- many1 baseDigit
        ; let n = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 digits
        ; seq n (return n)
        }          

-----------------------------------------------------------
-- Chars & Strings
-----------------------------------------------------------
charLiteral :: HParser Char
charLiteral     = lexeme (between (char '\'') 
                                  (char '\'' <?> "end of character")
                                  characterChar )
                <?> "character"

characterChar   = charLetter <|> charEscape 
                <?> "literal character"

charEscape      = do{ char '\\'; escapeCode }
charLetter      = satisfy (\c -> (c /= '\'') && (c /= '\\') && (c > '\026'))



stringLiteral :: HParser String
stringLiteral   = lexeme (
                  do{ str <- between (char '"')                   
                                     (char '"' <?> "end of string")
                                     (many stringChar) 
                    ; return (foldr (maybe id (:)) "" str)
                    }
                  <?> "literal string")

stringChar :: HParser (Maybe Char)
stringChar      =   do{ c <- stringLetter; return (Just c) }
                <|> stringEscape 
                <?> "string character"
            
stringLetter    = satisfy (\c -> (c /= '"') && (c /= '\\') && (c > '\026'))

stringEscape    = do{ char '\\'
                    ;     do{ escapeGap  ; return Nothing }
                      <|> do{ escapeEmpty; return Nothing }
                      <|> do{ esc <- escapeCode; return (Just esc) }
                    }
                    
escapeEmpty     = char '&'
escapeGap       = do{ many1 space
                    ; char '\\' <?> "end of string gap"
                    }
                    
                    
                    
-- escape codes
escapeCode :: HParser Char
escapeCode      = charEsc <|> charNum <|> charAscii <|> charControl
                <?> "escape code"

charControl, charNum, charEsc, charAscii :: HParser Char
charControl     = do{ char '^'
                    ; code <- large
                    ; return (toEnum (fromEnum code - fromEnum 'A'))
                    }

charNum         = do{ code <- decimal 
                              <|> do{ char 'o'; number 8 octDigit }
                              <|> do{ char 'x'; number 16 hexDigit }
                    ; return (toEnum (fromInteger code))
                    }

charEsc         = choice (map parseEsc escMap)
                where
                  parseEsc (c,code)     = do{ char c; return code }
                  
charAscii       = choice (map parseAscii asciiMap)
                where
                  parseAscii (asc,code) = try (do{ string asc; return code })


-- escape code tables
escMap          = zip ("abfnrtv\\\"\'") ("\a\b\f\n\r\t\v\\\"\'")
asciiMap        = zip (ascii3codes ++ ascii2codes) (ascii3 ++ ascii2) 

ascii2codes     = ["BS","HT","LF","VT","FF","CR","SO","SI","EM",
                   "FS","GS","RS","US","SP"]
ascii3codes     = ["NUL","SOH","STX","ETX","EOT","ENQ","ACK","BEL",
                   "DLE","DC1","DC2","DC3","DC4","NAK","SYN","ETB",
                   "CAN","SUB","ESC","DEL"]

ascii2          = ['\BS','\HT','\LF','\VT','\FF','\CR','\SO','\SI',
                   '\EM','\FS','\GS','\RS','\US','\SP']
ascii3          = ['\NUL','\SOH','\STX','\ETX','\EOT','\ENQ','\ACK',
                   '\BEL','\DLE','\DC1','\DC2','\DC3','\DC4','\NAK',
                   '\SYN','\ETB','\CAN','\SUB','\ESC','\DEL']

-----------------------------------------------------------
-- (Qualifed) identifiers
-- TODO: left factor the grammar for constructors, variables
-- and their qualified variants (instead of using "try").
-----------------------------------------------------------
tyvar   = varid  <?> "type variable"
tycon   = conid  <?> "type constructor"
tycls   = tycls  <?> "class name"
modid   = conid  <?> "module name (starting with upper-case letter)"

qtycon  = qconid <?> "type constructor"
qtycls  = qconid <?> "class name"

varid   = lexeme (try xvarid) <?> "variable"
conid   = lexeme (try xconid) <?> "constructor"
varsym  = lexeme (try xvarsym)<?> "variable"
consym  = lexeme (try xconsym)<?> "constructor"

qvarid  = qualify xvarid      <?> "variable"
qvarsym = qualify xvarsym     <?> "variable"
qconsym = qualify xconsym     <?> "constructor"

qconid  = lexeme (try (
          do{ id1 <- xconid
            ; do{ char '.'
                ; id2 <- xconid
                ; return (id1,id2)
                }
              <|> return ("",id1)
            }
          <?> "constructor"))

qualify p
  = lexeme (try (
        do{ id <- p; return ("",id) }
    <|> do{ mod <- xconid
          ; char '.'
          ; id  <- p
          ; return (mod,id)
          }))
    
-----------------------------------------------------------
-- Specials
-----------------------------------------------------------
special :: String -> HParser ()
special name
  = lexeme ( 
    do{ string name; 
        return () 
      }    
    <?> show name)

-----------------------------------------------------------
-- Operators & reserved ops
-----------------------------------------------------------
reservedOp :: String -> HParser ()
reservedOp name 
  = lexeme $ try $
    do{ string name
      ; notFollowedBy opsymbol <?> ("end of " ++ show name)
      }

xvarsym,xconsym :: HParser String
xvarsym
  = operator symbol 

xconsym
  = operator (char ':') 

operator :: HParser Char -> HParser String
operator start 
  = do{ c  <- start
      ; cs <- many opsymbol
      ; let name = c:cs 
      ; if (isReservedOp name)
         then unexpected ("reserved operator " ++ show name)
         else return name
      }

-----------------------------------------------------------
-- Identifiers & Reserved words
-----------------------------------------------------------
reserved :: String -> HParser ()
reserved name 
  = lexeme ( try (
    do{ string name
      ; notFollowedBy idsymbol <?> ("end of " ++ show name)
      }
    <?> show name))
      
xconid,xvarid :: HParser String
xvarid
  = do{ c  <- small
      ; cs <- many idsymbol
      ; let name = c:cs
      ; if (isReservedId name)
         then unexpected ("reserved word " ++ show name)
         else return name
      }
    
xconid
  = do{ c  <- large
      ; cs <- many idsymbol
      ; return (c:cs)
      }

-----------------------------------------------------------
-- Is reserved ?
-----------------------------------------------------------
isReservedId name
  = isReserved reservedIdNames name
        
isReservedOp name 
  = isReserved reservedOpNames name          
    
isReserved names name    
    = scan names
    where
      scan []       = False
      scan (r:rs)   = case (compare r name) of
                        LT  -> scan rs
                        EQ  -> True
                        GT  -> False


-----------------------------------------------------------
-- Character classes
-----------------------------------------------------------
opsymbol
  = symbol <|> char ':'

idsymbol
  = small <|> large <|> digit <|> char '\''

small
  = lower <|> char '_'

large
  = upper
      
-----------------------------------------------------------
-- Lexeme
-----------------------------------------------------------
lexeme :: HParser a -> HParser a -- AFIE
lexeme p =
    do { 
        onside; 
        x <- p; 
        pos <- getPosition;
        setLayoutState pos;
        whiteSpace; 
        return x;
    }

-----------------------------------------------------------
-- Whitespace
-----------------------------------------------------------   
toplevel p
  = do{ whiteSpace 
      ; x <- p
      ; eof
      ; return x
      }

whiteSpace :: HParser ()
whiteSpace 
  = skipMany (skipMany1 whiteChar <|> comment <|> ncomment <?> "")
            
whiteChar 
  = satisfy isWhite
  where
    isWhite c   = case c of ' '  -> True
                            '\n' -> True
                            '\t' -> True
                            '\r' -> True
                            '\v' -> True
                            '\f' -> True
                            _    -> False
                               
comment 
  = do{ try dashes
      ; skipMany (satisfy (\x -> x /= '\n'))
      ; return ()
      }

dashes
  = do{ string "--"
      ; skipMany (char '-')
      ; notFollowedBy symbol
      }

ncomment 
  = do { try (string "{-")
       ; incomment
       }

incomment 
    =   do{ try (string "-}");              return () }
    <|> do{ ncomment;                       incomment }
    <|> do{ skipMany1 (noneOf commentChar); incomment }
    <|> do{ oneOf commentChar;              incomment }
    <?> "end of comment"  
    where
      commentChar = "-{}"


-- AFIE
getLastPosition :: HParser SourcePos
getLastPosition =
    getLayoutState        