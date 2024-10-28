--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id: Lexer.hs 269 2012-08-31 15:16:49Z bastiaan $

module Helium.Lvm.Core.Parsing.Token
   ( Token
   , Lexeme(..)
   , Pos
   , incpos
   , newpos
   )
where

import           Text.PrettyPrint.Leijen        ( Pretty(..) )

-----------------------------------------------------------
-- Tokens and lexems
-----------------------------------------------------------

type Pos = (Int, Int)
type Token = (Pos, Lexeme)

data Lexeme     = LexUnknown Char
                | LexError String
                | LexChar Char
                | LexString String
                | LexInt Integer
                | LexFloat Double
                | LexId String
                | LexTypeVar Int
                | LexOp String
                | LexCon String
                | LexConOp String

                | LexCOMMA      -- ,
                | LexQUOTE      -- `
                | LexSEMI       -- ;
                | LexBSLASH     -- \ (niet meteen een enter hierachter vanwege -cpp)
                | LexASG        -- =
                | LexCOLON      -- :
                | LexCOLCOL     -- ::
                | LexDOT        -- .
                | LexDOTDOT     -- ..
                | LexBAR        -- |
                | LexLARROW     -- <-
                | LexRARROW     -- ->
                | LexTILDE      -- ~
                | LexARROW      -- =>
                | LexAT         -- @
                | LexEXCL       -- !
                | LexDASH       -- -

                | LexLPAREN     -- (
                | LexRPAREN     -- )
                | LexLBRACKET   -- [
                | LexRBRACKET   -- ]
                | LexLBRACE     -- {
                | LexRBRACE     -- }

                | LexLET
                | LexIN
                | LexDO
                | LexWHERE
                | LexCASE
                | LexOF
                | LexIF
                | LexTHEN
                | LexELSE
                | LexDATA
                | LexTYPE
                | LexNEWTYPE
                | LexMODULE
                | LexIMPORT
                | LexFORALL
                | LexEOF

                -- not standard
                | LexLETSTRICT
                | LexWITH

                | LexEXPORT
                | LexFROM
                | LexDEFAULT
                | LexCON

                | LexABSTRACT
                | LexINSTR
                | LexEXTERN

                | LexNOTHING
                | LexCUSTOM

                | LexSTATIC | LexDYNAMIC | LexRUNTIME
                | LexCCALL | LexSTDCALL | LexINSTRCALL
                | LexDECORATE | LexORDINAL
      deriving (Eq,Show)

instance Pretty Lexeme where
   pretty = pretty . show

-----------------------------------------------------------
-- Positions
-----------------------------------------------------------

incpos :: Pos -> Int -> Pos
incpos (line, col) i = (line, col + i)

newpos :: Pos -> Char -> Pos
newpos (line, _  ) '\n' = (line + 1, 1)
newpos (line, col) '\t' = (line, ((((col - 1) `div` 8) + 1) * 8) + 1)
newpos (line, col) _    = (line, col + 1)
