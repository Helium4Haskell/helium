module ParseMessage() where

import Messages hiding (Message)
import UHA_Syntax(Range(..), Position(..))

import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos

instance HasMessage ParseError where
    getMessage pe = 
        let msgs = errorMessages pe in
        MessageOneLiner (MessageString "Syntax error: ") :
        map (MessageOneLiner . MessageString . ("    "++)) (
            ( filter (not . null)
            . lines
            . showErrorMessages "or" "unknown parse error" 
                        "expecting" "unexpected" "end of input" 
            ) msgs
        )
    getRanges parseError =
        let pos = errorPos parseError
            name = sourceName pos; line = sourceLine pos; col = sourceColumn pos
            position = Position_Position name line col
        in [ Range_Range position position ]

