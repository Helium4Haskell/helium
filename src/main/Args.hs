module Args(Option(..), processArgs) where

import System
import Version
import Utils
import GetOpt

processArgs :: [String] -> IO ([Option], String)
processArgs args =
    let (options, arguments, errors) = getOpt Permute optionDescription args
    in if not (null errors) || length arguments /= 1 then do
        putStrLn $ "Helium compiler (" ++ version ++ ")"
        putStrLn (usageInfo "Usage: helium [options] file" optionDescription)
        exitWith (ExitFailure 1)
    else
        return (options, (head arguments))
    where
        optionDescription =
            [   Option "w" ["no-warnings"] (NoArg NoWarnings) "do not show warnings"
            ,   Option "b" ["build"] (NoArg Build) "recompile even if files are up to date"
            ,   Option "l" ["no-logging"] (NoArg NoLogging) "do not send log information"
            ,   Option "t" ["dump-types"] (NoArg DumpTypes) "show types of top-level functions"

#ifndef RELEASE
            ,   Option "u" ["dump-uha"] (NoArg DumpUHA) "pretty print abstract syntax tree"
            ,   Option "c" ["dump-core"] (NoArg DumpCore) "pretty print Core program"
            ,   Option "C" ["dump-core-to-file"] (NoArg DumpCoreToFile) "write Core program to file"
            ,   Option "d" ["dump-type-debug"] (NoArg DumpTypeDebug) "show type checker debugging information"
            
--            ,   Option "s" ["no-static-analysis"] (NoArg NoStaticAnalysis) "do not perform static analysis (dangerous!)"
            
            ,   Option "1" ["stop-after-parsing"] (NoArg StopAfterParser) "stop after parsing"
            ,   Option "2" ["stop-after-static-analysis"] (NoArg StopAfterStaticAnalysis) "stop after static analysis"
            ,   Option "3" ["stop-after-type-inferencing"] (NoArg StopAfterTypeInferencing) "stop after type inferencing"
            ,   Option "4" ["stop-after-desugaring"] (NoArg StopAfterDesugar) "stop after desugaring into Core"
            
            ,   Option "W" ["algorithm-w"]   (NoArg AlgorithmW) "use algorithm W for type inferencing"
            ,   Option "M" ["algorithm-m"]   (NoArg AlgorithmM) "use algorithm M for type inferencing"
            
            ,   Option "v" ["verbose"] (NoArg Verbose) "show the phase the compiler is in"
#endif
            ]

data Option
    = DumpUHA --
    | DumpCore --
    | DumpCoreToFile --
    | DumpTypes --
    | DumpTypeDebug
    
    | NoStaticAnalysis --
    | NoWarnings -- 
    | NoLogging --
    
    | StopAfterParser --
    | StopAfterStaticAnalysis --
    | StopAfterTypeInferencing    
    | StopAfterDesugar --
    
    | AlgorithmW --
    | AlgorithmM --
        
    | Verbose --
    | Build --
    deriving Eq
