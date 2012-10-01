{-| Module      :  PhaseParser
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Main.PhaseParser(phaseParser) where

import Main.CompileUtils
import Parser.LexerToken(Token)
import Parser.Parser (module_)
import Parser.ParseLibrary(runHParser)
import Text.ParserCombinators.Parsec.Error (ParseError)

phaseParser :: 
   String -> [Token] -> [Option] -> 
   Phase ParseError Module
phaseParser fullName tokens options = do
    enterNewPhase "Parsing" options
    case runHParser module_ fullName tokens True of
        Left parseError -> do
            return (Left [parseError])
        Right m ->
            return (Right m)