module TS_Compile where

import TS_CoreSyntax
import ImportEnvironment
import TS_ToCore      (typingStrategyToCore)
import System         (exitWith, ExitCode(..) )
import Directory      (doesFileExist)
import TS_Parser      (parseTypingStrategies)
import TS_Analyse     (analyseTypingStrategies)
import HeliumMessages (sortAndShowMessages)
import Monad          (unless, when)
import qualified Args (Option(..))

readTypingStrategiesFromFile :: [Args.Option] -> String -> ImportEnvironment -> IO Core_TypingStrategies
readTypingStrategiesFromFile options filename importEnvironment = 

   doesFileExist filename >>= 
   
     \exists -> if not exists then return [] else 
        
        do fileContent <- readFile filename            
           case parseTypingStrategies (operatorTable importEnvironment) filename fileContent of
              Left parseError -> do putStrLn ("Parse error in typing strategy: \n" ++ show parseError)
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
                       putStrLn ("Typing strategies...   (" ++ 
                          (if number == 1
                             then "1 strategy is included)"
                             else show number ++ " strategies are included)"))
              
                    return (map typingStrategyToCore typingStrategies)
