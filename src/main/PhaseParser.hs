module PhaseParser(phaseParser) where

import CompileUtils
import LexerToken(Token)
import qualified Parser(module_)
import ParseLibrary(runHParser)
import ParseMessage()

phaseParser :: String -> [String] -> [Token] -> [Option] -> IO Module
phaseParser fullName doneModules tokens options = do
    enterNewPhase "Parsing" options

    case runHParser Parser.module_ fullName tokens True of
        Left parseError -> do
            unless (NoLogging `elem` options) $ 
                sendLog "P" fullName doneModules options
            showErrorsAndExit [parseError] 1 options
        Right m ->
            return m

