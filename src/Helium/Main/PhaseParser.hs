{-| Module      :  PhaseParser
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseParser(phaseParser) where

import Helium.Main.CompileUtils
import Helium.Parser.LexerToken(Token)
import Helium.Parser.Parser (module_)
import Helium.Parser.ParseLibrary(runHParser)
import Text.ParserCombinators.Parsec.Error (ParseError)

phaseParser :: 
   String -> [Token] -> [Option] -> 
   Phase ParseError Module
phaseParser fullName tokens options = do
    enterNewPhase "Parsing" options
    case runHParser module_ fullName tokens True of
        Left parseError ->
            return (Left [parseError])
        Right m ->
            return (Right m)