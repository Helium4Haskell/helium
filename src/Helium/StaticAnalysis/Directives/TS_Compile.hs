-- | Module      :  TS_Compile
--    License     :  GPL
--
--    Maintainer  :  bastiaan@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable
--
-- 	Compile a .type file.
--
-- 	(directives based on "Scripting the Type Inference Process", ICFP 2003)
module Helium.StaticAnalysis.Directives.TS_Compile where

import Control.Monad (unless, when)
import Helium.CodeGeneration.CoreUtils
import qualified Helium.Main.Args as Args
import Helium.Main.Args
import Helium.ModuleSystem.ImportEnvironment
import Helium.Parser.Lexer (strategiesLexer)
import Helium.Parser.ParseMessage ()
import Helium.StaticAnalysis.Directives.TS_Analyse (analyseTypingStrategies)
import Helium.StaticAnalysis.Directives.TS_CoreSyntax
import Helium.StaticAnalysis.Directives.TS_Parser (parseTypingStrategies)
import Helium.StaticAnalysis.Directives.TS_ToCore (typingStrategyToCore)
import Helium.StaticAnalysis.Messages.HeliumMessages (sortAndShowMessages)
import Lvm.Core.Expr
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..), exitWith)

readTypingStrategiesFromFile ::
  [Args.Option] ->
  String ->
  ImportEnvironment ->
  IO (Core_TypingStrategies, [CoreDecl])
readTypingStrategiesFromFile options filename importEnvironment =
  doesFileExist filename
    >>= \exists ->
      if not exists
        then return ([], [])
        else do
          fileContent <- readFile filename
          case strategiesLexer options filename fileContent of
            Left lexError -> do
              putStrLn "Parse error in typing strategy: "
              putStr . sortAndShowMessages $ [lexError]
              exitWith (ExitFailure 1)
            Right (tokens, _) ->
              case parseTypingStrategies (operatorTable importEnvironment) filename tokens of
                Left parseError -> do
                  putStrLn "Parse error in typing strategy: "
                  putStr . sortAndShowMessages $ [parseError]
                  exitWith (ExitFailure 1)
                Right strategies ->
                  do
                    let (errors, warnings) = analyseTypingStrategies strategies importEnvironment
                    unless (null errors) $
                      do
                        putStr . sortAndShowMessages $ errors
                        exitWith (ExitFailure 1)
                    unless (Args.NoWarnings `elem` options || null warnings) $
                      do
                        putStrLn "\nWarnings in typing strategies:"
                        putStrLn . sortAndShowMessages $ warnings
                    let number = length strategies
                    when (Args.Verbose `elem` options && number > 0) $
                      putStrLn
                        ( "   ("
                            ++ ( if number == 1
                                   then "1 strategy is included)"
                                   else show number ++ " strategies are included)"
                               )
                        )
                    let coreTypingStrategies = map (typingStrategyToCore importEnvironment) strategies
                    when (containsDOption Type `any` options) $
                      do
                        putStrLn "Core typing strategies:"
                        mapM_ print coreTypingStrategies
                    return (coreTypingStrategies, [customStrategy (show coreTypingStrategies)])
