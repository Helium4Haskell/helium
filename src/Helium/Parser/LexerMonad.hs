{-| Module      :  LexerMonad
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Parser.LexerMonad
    ( LexerMonad
    , getPos, incPos, nextPos, addPos
    , openBracket, closeBracket, checkBracketsAtEOF
    , lexerError, lexerWarning
    , runLexerMonad
    , getOpts
    ) where

import Helium.Main.Args
import Helium.Parser.LexerMessage
import Text.ParserCombinators.Parsec.Pos

type Bracket = (SourcePos, Char)

-- Output monad: [LexerWarning]
-- State monad: SourcePos and [Bracket]
newtype LexerMonad a = 
    LM ([Option] -> SourcePos -> [Bracket] -> 
        Either LexerError (a, [LexerWarning], SourcePos, [Bracket]))

unLM :: LexerMonad t -> [Option] -> SourcePos -> [Bracket]
          -> Either LexerError (t, [LexerWarning], SourcePos, [Bracket])
unLM (LM x) = x

bindLM :: LexerMonad a -> (a -> LexerMonad b) -> LexerMonad b
bindLM (LM f) g = 
    LM (\opts pos brackets -> 
        case f opts pos brackets of
            Left err -> Left err
            Right (a, warnings, pos2, brackets2) -> 
                case unLM (g a) opts pos2 brackets2 of
                    Left err -> Left err
                    Right (b, moreWarnings, pos3, brackets3) ->
                        Right (b, warnings ++ moreWarnings, pos3, brackets3))

returnLM :: a -> LexerMonad a
returnLM x = LM (\_ pos brackets -> Right (x, [], pos, brackets))

instance Monad LexerMonad where
    (>>=) = bindLM
    return = returnLM

runLexerMonad :: [Option] -> String -> LexerMonad a -> Either LexerError (a, [LexerWarning])
runLexerMonad opts fileName (LM f) = 
    case f opts (initialPos fileName) [] of
        Left err -> Left err
        Right (a, warnings, _, _) -> Right (a, keepOneTabWarning warnings)

getOpts :: LexerMonad [Option]
getOpts = LM (\opts pos brackets -> Right (opts, [], pos, brackets))

getPos :: LexerMonad SourcePos
getPos = LM (\_ pos brackets -> Right (pos, [], pos, brackets))

incPos :: Int -> LexerMonad ()
incPos i = LM (\_ pos brackets -> Right ((), [], addPos i pos, brackets))

nextPos :: Char -> LexerMonad ()
nextPos c = LM (\_ pos brackets -> Right ( (), [], updatePosChar pos c, brackets ))

lexerError :: LexerErrorInfo -> SourcePos -> LexerMonad a
lexerError err pos = 
    LM (\_ _ _ -> Left (LexerError pos err))

lexerWarning :: LexerWarningInfo -> SourcePos -> LexerMonad ()
lexerWarning warning warningPos = 
    LM (\_ pos brackets -> 
        Right ((), [LexerWarning warningPos warning], pos, brackets))
    
addPos :: Int -> SourcePos -> SourcePos
addPos i pos = incSourceColumn pos i

openBracket :: Char -> LexerMonad ()
openBracket c = LM (\_ pos brackets ->
    Right ( (), [], pos, (pos, c) : brackets ))

closeBracket :: Char -> LexerMonad ()
closeBracket c = LM (\_ pos brackets ->
    case brackets of
        [] -> Left (LexerError pos (TooManyClose c))
        (pos2, c2):rest
            | matchBracket c2 c ->
                Right ((), [], pos, rest)
            | otherwise ->
                Left (LexerError pos (UnexpectedClose c pos2 c2))        
    )
    
checkBracketsAtEOF :: LexerMonad ()
checkBracketsAtEOF = LM (\_ pos brackets ->
    case brackets of
        [] -> Right ((), [], pos, [])
        _  -> Left (LexerError pos (StillOpenAtEOF brackets))
    )
    
matchBracket :: Char -> Char -> Bool
matchBracket '(' ')' = True
matchBracket '[' ']' = True
matchBracket '{' '}' = True
matchBracket _ _ = False
