{-| Module      :  PhaseLexer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module PhaseLexer(phaseLexer) where

import CompileUtils
import LexerToken(Token)
import Lexer
import LayoutRule(layout)

phaseLexer :: String -> [String] -> String -> [Option] -> 
                IO ([LexerWarning], [LexerWarning], [Token])
phaseLexer fullName doneModules contents options = do
    enterNewPhase "Lexing" options

    case lexer fullName contents of 
        Left lexError -> do
            unless (NoLogging `elem` options) $ 
                sendLog "L" fullName doneModules options
            showErrorsAndExit [lexError] 1 options
        Right (tokens, lexerWarnings) -> do
            let tokensWithLayout = layout tokens
                (lexerBeforeWarnings, lexerAfterWarnings) = splitWarnings lexerWarnings
            when (DumpTokens `elem` options) $ do
                putStrLn (show tokensWithLayout)
            return (lexerBeforeWarnings, lexerAfterWarnings, layout tokens)

