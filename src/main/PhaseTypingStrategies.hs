module PhaseTypingStrategies(phaseTypingStrategies) where

import CompileUtils
import Core(CoreDecl)
import TS_Compile (readTypingStrategiesFromFile)

phaseTypingStrategies :: String -> ImportEnvironment -> [ImportEnvironment] -> [Option] ->
                            IO (ImportEnvironment, [CoreDecl])
phaseTypingStrategies fullName localEnv importEnvs options

   | TypeInferenceDirectives `notElem` options = 
        return (removeTypingStrategies combinedEnvironment, [])

   | otherwise =
        let (path, baseName, _) = splitFilePath fullName
            fullNameNoExt       = combinePathAndFile path baseName            
        in do enterNewPhase "Type inference directives" options
              (typingStrategies, typingStrategiesDecls) <-
                 readTypingStrategiesFromFile options (fullNameNoExt ++ ".type") combinedEnvironment
              return 
                 ( addTypingStrategies typingStrategies combinedEnvironment
                 , typingStrategiesDecls
                 )              

 where 
   combinedEnvironment :: ImportEnvironment
   combinedEnvironment = foldr combineImportEnvironments localEnv importEnvs
