module ParseMessage() where

import Messages hiding (Message)
import UHA_Syntax(Range(..), Position(..))

import ParsecError
import ParsecPos

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

{-
sms msgs = show (map sm msgs)
  where
     sm (SysUnExpect s) = "SysUnExpect" ++ s
     sm (UnExpect    s) = "UnExpect" ++ s
     sm (Expect      s) = "Expect" ++ s
     sm (Message     s) = "Message" ++ s

specialCase :: [Message] -> Maybe [String]
specialCase msgs 
    | not (null charTexts) = Just
            [ head charTexts
            , "correct examples of character literals: 'a', '\\n', '%', ' ', '\\''"
            ]
    | not (null stringTexts) = Just
        [ head stringTexts
        , "correct examples of string literals: \"Helium\", \"10\", \"\", \"fun\\nny\\\"\""
        ]
    | not (null floatTexts) = Just
        [ head floatTexts
        , "correct examples of float-point literals: 1.0, 3.14159, 100.8, 0.00001"
        ]

    | not (null commentTexts) = Just
        [ head commentTexts ]

    where
        strings      = map messageString msgs 
        charTexts    = [ t | t <- charErrors, t `elem` strings ] 
        stringTexts  = [ t | t <- stringErrors, t `elem` strings ]
        floatTexts   = [ t | t <- floatErrors, t `elem` strings ]
        commentTexts = [ t | t <- commentErrors, t `elem` strings ]
specialCase _ = Nothing
-}
