module PhaseTypingStrategies(phaseTypingStrategies) where

import CompileUtils
import Core(CoreDecl)
import TS_Compile (readTypingStrategiesFromFile)

phaseTypingStrategies :: String -> ImportEnvironment -> [ImportEnvironment] -> [Option] ->
                            IO (ImportEnvironment, [CoreDecl])
phaseTypingStrategies fullName localEnv importEnvs options = do
    enterNewPhase "Typing strategies" options

    let (path, baseName, _) = splitFilePath fullName
        fullNameNoExt = combinePathAndFile path baseName

    let combinedEnvironment = foldr combineImportEnvironments localEnv importEnvs

    if TypingStrategy `notElem` options
      then
        return (removeTypingStrategies combinedEnvironment, [])
      else do
        (typingStrategies, typingStrategiesDecls) <-
            readTypingStrategiesFromFile options (fullNameNoExt ++ ".type") combinedEnvironment
        return 
            ( addTypingStrategies typingStrategies combinedEnvironment
            , typingStrategiesDecls
            )

