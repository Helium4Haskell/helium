--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Core.Parsing.Lexer
  ( lexer
  )
where

import           Control.Monad
import           Data.Char               hiding ( isSymbol
                                                , isLetter
                                                )
import           Data.List
import           Data.Maybe
import           Helium.Lvm.Core.Parsing.Token

type Lexer = Pos -> String -> [Token]
type Lexer5 = Pos -> String -> ([Token] -> [Token], Double, Pos, String)

lexer :: Lexer
lexer (ln, _) []               = [((ln + 1, 0), LexEOF)]

lexer pos     ('-' : '-' : cs) = nextinc lexeol pos 2 cs
lexer pos     ('{' : '-' : cs) = nextinc (lexComment 0) pos 2 cs

lexer pos ('l' : 'e' : 't' : '!' : cs) | nonId cs =
  (pos, LexLETSTRICT) : nextinc lexer pos 4 cs
lexer pos ('l' : 'e' : 't' : cs) | nonId cs =
  (pos, LexLET) : nextinc lexer pos 3 cs
lexer pos ('i' : 'n' : cs) | nonId cs = (pos, LexIN) : nextinc lexer pos 2 cs
lexer pos ('d' : 'o' : cs) | nonId cs = (pos, LexDO) : nextinc lexer pos 2 cs
lexer pos ('w' : 'h' : 'e' : 'r' : 'e' : cs) | nonId cs =
  (pos, LexWHERE) : nextinc lexer pos 5 cs
lexer pos ('c' : 'a' : 's' : 'e' : cs) | nonId cs =
  (pos, LexCASE) : nextinc lexer pos 4 cs
lexer pos ('o' : 'f' : cs) | nonId cs = (pos, LexOF) : nextinc lexer pos 2 cs
lexer pos ('i' : 'f' : cs) | nonId cs = (pos, LexIF) : nextinc lexer pos 2 cs
lexer pos ('t' : 'h' : 'e' : 'n' : cs) | nonId cs =
  (pos, LexTHEN) : nextinc lexer pos 4 cs
lexer pos ('e' : 'l' : 's' : 'e' : cs) | nonId cs =
  (pos, LexELSE) : nextinc lexer pos 4 cs
lexer pos ('d' : 'a' : 't' : 'a' : cs) | nonId cs =
  (pos, LexDATA) : nextinc lexer pos 4 cs
lexer pos ('t' : 'y' : 'p' : 'e' : cs) | nonId cs =
  (pos, LexTYPE) : nextinc lexer pos 4 cs
lexer pos ('n' : 'e' : 'w' : 't' : 'y' : 'p' : 'e' : cs) | nonId cs =
  (pos, LexNEWTYPE) : nextinc lexer pos 7 cs
lexer pos ('m' : 'o' : 'd' : 'u' : 'l' : 'e' : cs) | nonId cs =
  (pos, LexMODULE) : nextinc lexer pos 6 cs
lexer pos ('i' : 'm' : 'p' : 'o' : 'r' : 't' : cs) | nonId cs =
  (pos, LexIMPORT) : nextinc lexer pos 6 cs
lexer pos ('f' : 'o' : 'r' : 'a' : 'l' : 'l' : cs) | nonId cs =
  (pos, LexFORALL) : nextinc lexer pos 6 cs
-- not standard
lexer pos ('c' : 'o' : 'n' : cs) | nonId cs =
  (pos, LexCON) : nextinc lexer pos 3 cs
lexer pos ('w' : 'i' : 't' : 'h' : cs) | nonId cs =
  (pos, LexWITH) : nextinc lexer pos 4 cs
lexer pos ('c' : 'c' : 'a' : 'l' : 'l' : cs) | nonId cs =
  (pos, LexCCALL) : nextinc lexer pos 5 cs
lexer pos ('e' : 'x' : 'p' : 'o' : 'r' : 't' : cs) | nonId cs =
  (pos, LexEXPORT) : nextinc lexer pos 6 cs
lexer pos ('f' : 'r' : 'o' : 'm' : cs) | nonId cs =
  (pos, LexFROM) : nextinc lexer pos 4 cs
lexer pos ('e' : 'x' : 't' : 'e' : 'r' : 'n' : cs) | nonId cs =
  (pos, LexEXTERN) : nextinc lexer pos 6 cs
lexer pos ('s' : 't' : 'a' : 't' : 'i' : 'c' : cs) | nonId cs =
  (pos, LexSTATIC) : nextinc lexer pos 6 cs
lexer pos ('c' : 'u' : 's' : 't' : 'o' : 'm' : cs) | nonId cs =
  (pos, LexCUSTOM) : nextinc lexer pos 6 cs
lexer pos ('n' : 'o' : 't' : 'h' : 'i' : 'n' : 'g' : cs) | nonId cs =
  (pos, LexNOTHING) : nextinc lexer pos 7 cs
lexer pos ('d' : 'e' : 'f' : 'a' : 'u' : 'l' : 't' : cs) | nonId cs =
  (pos, LexDEFAULT) : nextinc lexer pos 7 cs
lexer pos ('d' : 'y' : 'n' : 'a' : 'm' : 'i' : 'c' : cs) | nonId cs =
  (pos, LexDYNAMIC) : nextinc lexer pos 7 cs
lexer pos ('r' : 'u' : 'n' : 't' : 'i' : 'm' : 'e' : cs) | nonId cs =
  (pos, LexRUNTIME) : nextinc lexer pos 7 cs
lexer pos ('s' : 't' : 'd' : 'c' : 'a' : 'l' : 'l' : cs) | nonId cs =
  (pos, LexSTDCALL) : nextinc lexer pos 7 cs
lexer pos ('o' : 'r' : 'd' : 'i' : 'n' : 'a' : 'l' : cs) | nonId cs =
  (pos, LexORDINAL) : nextinc lexer pos 7 cs
lexer pos ('d' : 'e' : 'c' : 'o' : 'r' : 'a' : 't' : 'e' : cs) | nonId cs =
  (pos, LexDECORATE) : nextinc lexer pos 8 cs
lexer pos ('a' : 'b' : 's' : 't' : 'r' : 'a' : 'c' : 't' : cs) | nonId cs =
  (pos, LexABSTRACT) : nextinc lexer pos 8 cs
lexer pos ('i' : 'n' : 's' : 't' : 'r' : 'c' : 'a' : 'l' : 'l' : cs)
  | nonId cs = (pos, LexINSTRCALL) : nextinc lexer pos 9 cs
lexer pos ('i' : 'n' : 's' : 't' : 'r' : 'u' : 'c' : 't' : 'i' : 'o' : 'n' : cs)
  | nonId cs
  = (pos, LexINSTR) : nextinc lexer pos 11 cs
lexer pos ('v' : '$' : cs) | num /= "" && nonId cs' =
  (pos, LexTypeVar $ foldl (\x y -> x * 10 + (fromEnum y - fromEnum '0')) 0 num)
    : nextinc lexer pos (2 + length num) cs'
 where
  cs' = dropWhile isDigit cs
  num = takeWhile isDigit cs

lexer pos (':' : ':' : cs) | nonSym cs =
  (pos, LexCOLCOL) : nextinc lexer pos 2 cs
lexer pos ('=' : '>' : cs) | nonSym cs =
  (pos, LexARROW) : nextinc lexer pos 2 cs
lexer pos ('-' : '>' : cs) | nonSym cs =
  (pos, LexRARROW) : nextinc lexer pos 2 cs
lexer pos ('<' : '-' : cs) | nonSym cs =
  (pos, LexLARROW) : nextinc lexer pos 2 cs
lexer pos ('.' : '.' : cs) | nonSym cs =
  (pos, LexDOTDOT) : nextinc lexer pos 2 cs
lexer pos ('\'' : '\'' : cs)      = nextinc (lexSpecialId pos) pos 2 cs

lexer pos ('.' : cs) | nonSym cs  = (pos, LexDOT) : nextinc lexer pos 1 cs
lexer pos (',' : cs) | nonSym cs  = (pos, LexCOMMA) : nextinc lexer pos 1 cs
lexer pos ('`' : cs) | nonSym cs  = (pos, LexQUOTE) : nextinc lexer pos 1 cs
lexer pos (';' : cs) | nonSym cs  = (pos, LexSEMI) : nextinc lexer pos 1 cs
lexer pos ('|' : cs) | nonSym cs  = (pos, LexBAR) : nextinc lexer pos 1 cs
lexer pos ('~' : cs) | nonSym cs  = (pos, LexTILDE) : nextinc lexer pos 1 cs
lexer pos ('@' : cs) | nonSym cs  = (pos, LexAT) : nextinc lexer pos 1 cs
lexer pos ('=' : cs) | nonSym cs  = (pos, LexASG) : nextinc lexer pos 1 cs
lexer pos ('\\' : cs) | nonSym cs = (pos, LexBSLASH) : nextinc lexer pos 1 cs
lexer pos ('!' : cs) | nonSym cs  = (pos, LexEXCL) : nextinc lexer pos 1 cs
lexer pos (':' : cs) | nonSym cs  = (pos, LexCOLON) : nextinc lexer pos 1 cs
-- lexer pos ('-':cs)              | nonSym cs = (pos,LexDASH)   : nextinc lexer pos 1 cs

lexer pos (   '('  : cs)          = (pos, LexLPAREN) : nextinc lexer pos 1 cs
lexer pos (   ')'  : cs)          = (pos, LexRPAREN) : nextinc lexer pos 1 cs
lexer pos (   '['  : cs)          = (pos, LexLBRACKET) : nextinc lexer pos 1 cs
lexer pos (   ']'  : cs)          = (pos, LexRBRACKET) : nextinc lexer pos 1 cs
lexer pos (   '{'  : cs)          = (pos, LexLBRACE) : nextinc lexer pos 1 cs
lexer pos (   '}'  : cs)          = (pos, LexRBRACE) : nextinc lexer pos 1 cs

lexer pos (   '\'' : cs)          = nextinc lexChar pos 1 cs
lexer pos (   '"'  : cs)          = lexString (incpos pos 1) (pos, "") cs

lexer pos (   '0'  : cs)          = lexZero pos cs

lexer pos xs@(':'  : _ )          = lexWhile isSymbol LexConOp pos pos xs
lexer pos ('$' : xs@(c : _)) | isLower c || c == '_' =
  let np = incpos pos 1 in lexWhile isLetter LexId np np xs
lexer pos xs@(c : cs)
  | isLower c || c == '_' = lexWhile isLetter LexId pos pos xs
  | isUpper c             = lexConOrQual pos xs
  | isSpace c             = next lexer pos c cs
  | isSymbol c            = lexWhile isSymbol LexOp pos pos xs
  | isDigit c             = lexIntFloat pos xs
  | otherwise             = (pos, LexUnknown c) : next lexer pos c cs

next :: (Pos -> String -> a) -> Pos -> Char -> String -> a
next f pos c cs = let pos' = newpos pos c in seq pos' (f pos' cs)

nextinc :: (Pos -> String -> a) -> Pos -> Int -> String -> a
nextinc f pos i cs = let pos' = incpos pos i in seq pos' (f pos' cs)

lexConOrQual :: Lexer
lexConOrQual pos cs =
  let (ident, rest) = span isLetter cs
      pos'          = foldl' newpos pos ident
  in  case rest of
        '.' : ds@(d : _)
          | isLower d || d == '_' -> lexWhile isLetter
                                              (\n -> LexId $ ident ++ "." ++ n)
                                              pos
                                              (incpos pos' 1)
                                              ds
          | isUpper d -> lexWhile isLetter
                                  (\n -> LexCon $ ident ++ "." ++ n)
                                  pos
                                  (incpos pos' 1)
                                  ds
          | isSymbol d -> lexWhile isSymbol
                                   (\n -> LexId $ ident ++ "." ++ n)
                                   pos
                                   (incpos pos' 1)
                                   ds
        '.' : '\'' : '\'' : ds -> case lexSpecialId pos (incpos pos 3) ds of
          (pos1, LexCon s) : xs -> (pos1, LexCon $ ident ++ "." ++ s) : xs
          (pos1, LexId s ) : xs -> (pos1, LexId  $ ident ++ "." ++ s) : xs
          xs                    -> xs
        _ -> (pos, LexCon ident) : seq pos' (lexer pos' rest)

lexWhile :: (Char -> Bool) -> (String -> Lexeme) -> Pos -> Lexer
lexWhile ctype con pos0 pos cs =
  let (ident, rest) = span ctype cs
      pos'          = foldl' newpos pos ident
  in  (pos0, con ident) : seq pos' (lexer pos' rest)

lexSpecialId :: Pos -> Lexer
lexSpecialId originalPos pos cs =
  let (ident, rest) = span (\c -> not (isSpace c) && c /= '\'') cs
  in
    case rest of
      ('\'' : '\'' : cs') ->
        let pos' = foldl' newpos pos (ident ++ "''")
        in
          seq pos' $ case ident of
            [] ->
              (originalPos, LexError "empty special identifier")
                : lexer pos' cs'
            -- ":"       -> (originalPos,LexError "empty special con identifier") : lexer pos' cs'
            ":"         -> (originalPos, LexId ident) : lexer pos' cs'
            ':' : conid -> (originalPos, LexCon conid) : lexer pos' cs'
            _           -> (originalPos, LexId ident) : lexer pos' cs'
      _ ->
        let pos' = foldl' newpos pos ident
        in  ( pos'
            , LexError ("expecting '' after special identifier " ++ show ident)
            )
              : lexer pos' rest -- originalPos points to where '' started. it should
                                -- be used as the position of the identifier because of the layout rule
                                -- y = 4
                                -- ''x'' = 3   -- x and y should be in the same context

-----------------------------------------------------------
-- Numbers
-----------------------------------------------------------

lexZero :: Lexer
lexZero pos (c : cs)
  | c == 'o' || c == 'O' = case octal pos' cs of
    Just (i, pos'', cs') -> (pos, LexInt i) : lexer pos'' cs'
    Nothing -> (pos, LexError "illegal octal number") : lexer pos' cs
  | c == 'x' || c == 'X' = case hexal pos' cs of
    Just (i, pos'', cs') -> (pos, LexInt i) : lexer pos'' cs'
    Nothing -> (pos, LexError "illegal hexadecimal number") : lexer pos' cs
  | c == '.' = lexFloat 0 pos' cs
  | isDigit c = lexIntFloat pos (c : cs)
  | otherwise = (pos, LexInt 0) : lexer pos' (c : cs)
  where pos' = newpos (newpos pos '0') c
lexZero pos cs = (pos, LexInt 0) : lexer (newpos pos '0') cs

lexIntFloat :: Lexer
lexIntFloat pos cs = case decimal pos cs of
  Just (i, pos', cs') -> case cs' of
    ('.' : cs'') -> lexFloat i (newpos pos' '.') cs''
    _            -> (pos, LexInt i) : lexer pos' cs'
  _ -> error "lexIntFloat"

lexFloat :: Integer -> Lexer
lexFloat i pos cs =
  let (fracterr, fract, pos' , cs' ) = lexFract pos cs
      (experr  , expon, pos'', cs'') = lexExponent pos' cs'
  in  fracterr
        (experr
          ((pos, LexFloat ((fromInteger i + fract) * expon)) : lexer pos'' cs'')
        )

lexFract :: Lexer5
lexFract pos cs =
  let (xs, rest) = span isDigit cs
  in  if null xs
        then (((pos, LexError "invalid fraction") :), 0.0, pos, cs)
        else (id, foldr op 0.0 xs, foldl' newpos pos xs, rest)
  where c `op` f = (f + fromIntegral (fromEnum c - fromEnum '0')) / 10.0

lexExponent :: Lexer5
lexExponent pos (c : cs) | c == 'e' || c == 'E' = case cs of
  ('-' : cs') -> lexExp negate (incpos pos 2) cs'
  ('+' : cs') -> lexExp id (incpos pos 2) cs'
  _           -> lexExp id (incpos pos 1) cs
lexExponent pos cs = (id, 1.0, pos, cs)

lexExp :: (Integer -> Integer) -> Lexer5
lexExp f pos cs = case decimal pos cs of
  Just (i, pos', cs') -> (id, power (f i), pos', cs')
  Nothing             -> (((pos, LexError "invalid exponent") :), 1.0, pos, cs)
 where
  power e | e < 0     = 1.0 / power (-e)
          | otherwise = fromInteger (10 ^ e)

hexal, octal, decimal :: Pos -> String -> Maybe (Integer, Pos, String)
hexal = number 16 isHexal
octal = number 8 isOctal
decimal = number 10 isDigit

number
  :: Integer -> (Char -> Bool) -> Pos -> String -> Maybe (Integer, Pos, String)
number base test pos cs =
  let (xs, rest) = span test cs
  in  if null xs
        then Nothing
        else Just (foldl' op 0 xs, foldl' newpos pos xs, rest)
 where
  x `op` y = base * x + fromIntegral (fromChar y)
  fromChar c | isDigit c = fromEnum c - fromEnum '0'
             | otherwise = fromEnum (toUpper c) - fromEnum 'A'

isOctal, isHexal :: Char -> Bool
isOctal = isOctDigit
isHexal = isHexDigit

-----------------------------------------------------------
-- Characters
-----------------------------------------------------------

lexChar :: Lexer
lexChar pos ('\\' : cs) =
  let (pos', lexeme, xs) = escapeChar pos cs in lexEndChar lexeme pos' xs
lexChar pos ('\'' : cs) =
  (pos, LexError "empty character") : nextinc lexer pos 1 cs

lexChar pos (c : cs)
  | isGraphic c || c == '"' || c == ' ' = lexEndChar (pos, LexChar c)
                                                     (incpos pos 1)
                                                     cs
  | otherwise = (pos, LexError "invalid character") : next lexer pos c cs

lexChar pos [] =
  (pos, LexError "unexpected end of input in character") : lexer pos []

lexEndChar :: Token -> Lexer
lexEndChar lexeme pos ('\'' : cs) = lexeme : nextinc lexer pos 1 cs
lexEndChar _ pos cs =
  (pos, LexError "expecting termiInting symbol \"'\"") : lexer pos cs


lexString :: Pos -> (Pos, String) -> String -> [Token]
lexString pos (p, s) ('"' : cs) =
  (p, LexString (reverse s)) : nextinc lexer pos 1 cs

lexString pos (p, s) ('\n' : cs) =
  (p, LexString (reverse s))
    : (pos, LexError "newline in string")
    : next lexer pos '\n' cs

lexString pos (p, s) ('\\' : c : cs)
  | isSpace c
  = gap (incpos pos 1) (p, s) cs
  | c == '&'
  = lexString (incpos pos 2) (p, s) cs
  | otherwise
  = let (pos', (_, lexeme), cs') = escapeChar pos (c : cs)
    in
      case lexeme of
        LexChar d -> lexString pos' (p, d : s) cs'
        _ ->
          (pos, LexError "illegal escape sequence") : lexString pos' (p, s) cs'

lexString pos (p, s) [] =
  (p, LexString (reverse s))
    : (pos, LexError "unexpected end of input in string")
    : lexer pos []
lexString pos (p, s) ['\\'] = lexString (incpos pos 1) (p, s) []

lexString pos (p, s) (c : cs)
  | isGraphic c || c == '\'' || c == ' '
  = lexString (incpos pos 1) (p, c : s) cs
  | otherwise
  = (pos, LexError ("illegal character (" ++ [c] ++ ") in string"))
    : lexString (newpos pos c) (p, s) cs

gap :: Pos -> (Pos, String) -> String -> [Token]
gap pos (p, s) cs =
  let (ws, rest) = span isSpace cs
      pos'       = foldl' newpos pos ws
  in  case rest of
        ('\\' : cs') -> lexString pos' (p, s) cs'
        _ ->
          (pos', LexError "(\\) expected at end of gap")
            : lexString pos' (p, s) rest

-----------------------------------------------------------
-- Escape sequences
-----------------------------------------------------------


escapeChar :: Pos -> String -> (Pos, Token, String)
escapeChar pos [] = (pos, (pos, LexError "Unexpected end of input"), [])
escapeChar pos cs = fromMaybe def (msum [ f pos cs | f <- fs ])
 where
  def = (pos, (pos, LexError "invalid escape sequence"), cs)
  fs  = [ascii3, ascii2, escape, control, charnum]

charnum :: Pos -> String -> Maybe (Pos, Token, String)
charnum pos ('x' : cs)           = numToChar pos (hexal (incpos pos 1) cs)
charnum pos ('o' : cs)           = numToChar pos (octal (incpos pos 1) cs)
charnum pos ('d' : cs)           = numToChar pos (decimal (incpos pos 1) cs)
charnum pos (c : cs) | isDigit c = numToChar pos (decimal (incpos pos 1) cs)
charnum _ _                      = Nothing

numToChar :: Pos -> Maybe (Integer, Pos, String) -> Maybe (Pos, Token, String)
numToChar pos (Just (x, pos', cs')) =
  Just (pos', (pos, LexChar (toEnum (fromInteger x))), cs')
numToChar _ _ = Nothing



control :: Pos -> String -> Maybe (Pos, Token, String)
control pos ('^' : c : cs) | isUpper c =
  let x = toEnum (fromEnum c - fromEnum 'A')
  in  Just (incpos pos 2, (pos, LexChar x), cs)
control _ _ = Nothing



escape :: Pos -> String -> Maybe (Pos, Token, String)
escape pos (c : cs) = case lookup c escapemap of
  Just k  -> Just (incpos pos 1, (pos, LexChar k), cs)
  Nothing -> Nothing
escape _ _ = Nothing

ascii2 :: Pos -> String -> Maybe (Pos, Token, String)
ascii2 pos (x : y : cs) = case lookup [x, y] ascii2map of
  Just k  -> Just (incpos pos 2, (pos, LexChar k), cs)
  Nothing -> Nothing
ascii2 _ _ = Nothing

ascii3 :: Pos -> String -> Maybe (Pos, Token, String)
ascii3 pos (x : y : z : cs) = case lookup [x, y, z] ascii3map of
  Just k  -> Just (incpos pos 3, (pos, LexChar k), cs)
  Nothing -> Nothing
ascii3 _ _ = Nothing



escapemap :: [(Char, Char)]
escapemap = zip "abfnrtv\\\"\'" "\a\b\f\n\r\t\v\\\"\'"

ascii2map :: [(String, Char)]
ascii2map = zip
  [ "BS"
  , "HT"
  , "LF"
  , "VT"
  , "FF"
  , "CR"
  , "SO"
  , "SI"
  , "EM"
  , "FS"
  , "GS"
  , "RS"
  , "US"
  , "SP"
  ]
  "\BS\HT\LF\VT\FF\CR\SO\SI\EM\FS\GS\RS\US\SP"

ascii3map :: [(String, Char)]
ascii3map = zip
  [ "NUL"
  , "SOH"
  , "STX"
  , "ETX"
  , "EOT"
  , "ENQ"
  , "ACK"
  , "BEL"
  , "DLE"
  , "DC1"
  , "DC2"
  , "DC3"
  , "DC4"
  , "NAK"
  , "SYN"
  , "ETB"
  , "CAN"
  , "SUB"
  , "ESC"
  , "DEL"
  ]
  "\NUL\SOH\STX\ETX\EOT\ENQ\ACK\BEL\DLE\DC1\DC2\DC3\DC4\NAK\SYN\ETB\CAN\SUB\ESC\DEL"


-----------------------------------------------------------
-- Symbols
-----------------------------------------------------------

isSpecial, isSmall, isLarge, isLetter, isSymbol :: Char -> Bool
isSpecial = (`elem` "(),;[]`{}")
isSmall c = isLower c || c == '_'
isLarge = isUpper
isLetter c = isSmall c || isLarge c || isDigit c || c == '\''
isSymbol = (`elem` "!#$%&*+./<=>?@\\^|-~:")

isGraphic :: Char -> Bool
isGraphic c =
  isLetter c || isSymbol c || isSpecial c || (c == ':') || (c == '"')

nonId :: String -> Bool
nonId (c : _) = not (isLetter c)
nonId []      = True

nonSym :: String -> Bool
nonSym (c : _) = not (isSymbol c)
nonSym []      = True

-----------------------------------------------------------
-- Comment
-----------------------------------------------------------

lexeol :: Lexer
lexeol pos ('\n' : cs) = lexer (newpos pos '\n') cs
lexeol pos (c    : cs) = lexeol (newpos pos c) cs
lexeol pos []          = lexer pos []

lexComment :: Int -> Lexer
lexComment level pos s = case s of
  '-' : '}' : cs | level == 0 -> lexer (incpos pos 2) cs
                 | otherwise  -> lexComment (level - 1) (incpos pos 2) cs
  '{' : '-' : cs -> lexComment (level + 1) (incpos pos 2) cs
  c         : cs -> lexComment level (newpos pos c) cs
  []             -> lexer pos []
