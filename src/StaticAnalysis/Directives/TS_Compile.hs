{-| Module      :  TS_Compile
    License     :  GPL

    Maintainer  :  bastiaan@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

	Compile a .type file.
	
	(directives based on "Scripting the Type Inference Process", ICFP 2003)
-}

module StaticAnalysis.Directives.TS_Compile where

import StaticAnalysis.Directives.TS_CoreSyntax
import ModuleSystem.ImportEnvironment
import StaticAnalysis.Directives.TS_ToCore      (typingStrategyToCore)
import System.Exit         (exitWith, ExitCode(..) )
import System.Directory      (doesFileExist)
import StaticAnalysis.Directives.TS_Parser      (parseTypingStrategies)
import Parser.Lexer          (strategiesLexer)
import StaticAnalysis.Directives.TS_Analyse     (analyseTypingStrategies)
import StaticAnalysis.Messages.HeliumMessages (sortAndShowMessages)
import Control.Monad          (unless, when)
import qualified Main.Args as Args
import Parser.ParseMessage ()
import CodeGeneration.CoreUtils
import Lvm.Core.Expr

readTypingStrategiesFromFile :: [Args.Option] -> String -> ImportEnvironment -> 
    IO (Core_TypingStrategies, [CoreDecl])
readTypingStrategiesFromFile options filename importEnvironment =

   doesFileExist filename >>= 
   
     \exists -> if not exists then return ([], []) else 
        
        do fileContent <- readFile filename            
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
                  Right typingStrategies -> 

                     do let (errors, warnings) = analyseTypingStrategies typingStrategies importEnvironment

                        unless (null errors) $ 
                           do putStr . sortAndShowMessages $ errors
                              exitWith (ExitFailure 1)

                        unless (Args.NoWarnings `elem` options || null warnings) $
                           do putStrLn "\nWarnings in typing strategies:"
                              putStrLn . sortAndShowMessages $ warnings

                        let number = length typingStrategies
                        when (Args.Verbose `elem` options && number > 0) $
                           putStrLn ("   (" ++ 
                              (if number == 1
                                 then "1 strategy is included)"
                                 else show number ++ " strategies are included)")) 

                        let coreTypingStrategies = map (typingStrategyToCore importEnvironment) typingStrategies
                        when (Args.DumpTypeDebug `elem` options) $
                           do putStrLn "Core typing strategies:"
                              mapM_ print coreTypingStrategies
                        
                        return ( coreTypingStrategies, [ customStrategy (show coreTypingStrategies) ] )
