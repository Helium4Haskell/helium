{-| Module      :  Args
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Args
    ( Option(..)
    , processArgs
    , lvmPathFromOptions
    ) where

import System
import Version
import Utils
import Data.Char
import System.Console.GetOpt

processArgs :: [String] -> IO ([Option], String)
processArgs args =
    let (options, arguments, errors) = getOpt Permute (optionDescription True) args
    in if not (null errors) || length arguments /= 1 then do
        putStrLn $ "Helium compiler " ++ version
        putStrLn (usageInfo "Usage: helium [options] file" (optionDescription (AllOptions `elem` options)))
        exitWith (ExitFailure 1)
    else
        return (options, (head arguments))
    where
        optionDescription allOptions =
            [   Option "w" ["no-warnings"] (NoArg NoWarnings) "do not show warnings"
            ,   Option "b" ["build"] (NoArg BuildOne) "recompile module even if up to date"
            ,   Option "B" ["build-all"] (NoArg BuildAll) "recompile all modules even if up to date"
            ,   Option "l" ["no-logging"] (NoArg NoLogging) "do not send log information"
            ,   Option "i" ["dump-information"]     (NoArg DumpInformationForThisModule) "show information about this module"
            ,   Option "I" ["dump-all-information"] (NoArg DumpInformationForAllModules) "show information about all imported modules"
            ,   Option "P" ["lvmpath"] (ReqArg LvmPath "PATH") "use PATH as search path"
            ,   Option "v" ["verbose"] (NoArg Verbose) "show the phase the compiler is in"
            ,   Option "X" ["all-options"] (NoArg AllOptions) "show all compiler options"
            ]
            ++
            if not allOptions then [] else
            [   Option "t" ["dump-tokens"] (NoArg DumpTokens) "dump tokens to screen"
            ,   Option "u" ["dump-uha"] (NoArg DumpUHA) "pretty print abstract syntax tree"
            ,   Option "c" ["dump-core"] (NoArg DumpCore) "pretty print Core program"
            ,   Option "C" ["save-core"] (NoArg DumpCoreToFile) "write Core program to file"
            ,   Option "d" ["dump-type-debug"] (NoArg DumpTypeDebug) "show type checker debug information"
            ,   Option "L" ["debug-logger"] (NoArg DebugLogger) "show logger debug information"
                        
            ,   Option "1" ["stop-after-parsing"] (NoArg StopAfterParser) "stop after parsing"
            ,   Option "2" ["stop-after-static-analysis"] (NoArg StopAfterStaticAnalysis) "stop after static analysis"
            ,   Option "3" ["stop-after-type-inferencing"] (NoArg StopAfterTypeInferencing) "stop after type inferencing"
            ,   Option "4" ["stop-after-desugaring"] (NoArg StopAfterDesugar) "stop after desugaring into Core"
            
            ,   Option "W" ["algorithm-w"] (NoArg AlgorithmW)              "use algorithm W for type inferencing"
            ,   Option "M" ["algorithm-m"] (NoArg AlgorithmM)              "use algorithm M for type inferencing"
            ,   Option ""  ["no-directives" ] (NoArg DisableDirectives)    "disable type inference directives"
            ,   Option "K" ["kind-inferencing"] (NoArg KindInferencing)    "do kind inferencing"
            ,   Option ""  ["overloading"] (NoArg Overloading)             "turn overloading on (experimental)"
            ,   Option ""  ["signature-warnings"] (NoArg SignatureWarnings)  "warn for too specific signatures"  

            -- available solvers for type inferencing     
            ,   Option "" ["solver-simple"     ] (NoArg SolverSimple     ) "a straightforward implementation"
            ,   Option "" ["solver-greedy"     ] (NoArg SolverGreedy     ) "a fast solver"
            ,   Option "" ["solver-typegraph"  ] (NoArg SolverTypeGraph  ) "slow, but high quality error messages"
            ,   Option "" ["solver-combination"] (NoArg SolverCombination) "combines \"greedy\" and \"type graph\""
            ,   Option "" ["solver-chunks"     ] (NoArg SolverChunks     ) "solves chunks of constraints (default)"
            
            -- available treewalks for type inferencing
            ,   Option "" ["treewalk-topdown" ] (NoArg TreeWalkTopDown            ) "top down treewalk"
            ,   Option "" ["treewalk-bottomup"] (NoArg TreeWalkBottomUp           ) "bottom up treewalkt"
            ,   Option "" ["treewalk-inorder1"] (NoArg TreeWalkInorderTopFirstPre ) "top;upward;child"
            ,   Option "" ["treewalk-inorder2"] (NoArg TreeWalkInorderTopLastPre  ) "upward;child;top"
            ,   Option "" ["treewalk-inorder3"] (NoArg TreeWalkInorderTopFirstPost) "top;child;upward"
            ,   Option "" ["treewalk-inorder4"] (NoArg TreeWalkInorderTopLastPost ) "child;upward;top"
            
            -- other options for type inferencing
            ,   Option "" ["right-to-left"] (NoArg RightToLeft) "right-to-left treewalk"
            ,   Option "" ["no-spreading" ] (NoArg NoSpreading) "do not spread type constraints"
	    
            -- options for type graph heuristics
            ,   Option "" ["no-repair-heuristics"]     (NoArg NoRepairHeuristics) "don't suggest program fixes"
            ,   Option "" ["unifier-heuristics"]       (NoArg UnifierHeuristics)  "use unifier heuristics (experimental)"
            ,   Option "" ["select-constraint-number"] (ReqArg selectCNR "CNR")   "select constraint number to be reported"
            ,   Option "" ["dump-type-inspector"]      (NoArg DumpTypeInspector)  "dump information for TypeInspector"
            ]

data Option
    = DumpTokens
    | DumpUHA --
    | DumpCore --
    | DumpCoreToFile --
    | DumpInformationForThisModule
    | DumpInformationForAllModules
    | DumpTypeDebug
    | DumpTypeInspector
    | DebugLogger
    | AllOptions
    | Verbose --
    | BuildOne --
    | BuildAll    
    | LvmPath String
    | NoWarnings -- 
    | NoLogging --
    
    | StopAfterParser --
    | StopAfterStaticAnalysis --
    | StopAfterTypeInferencing    
    | StopAfterDesugar --
    
    -- type inference constraint solvers
    | SolverSimple | SolverGreedy | SolverTypeGraph | SolverCombination | SolverChunks  
    -- type inference tree walks
    | TreeWalkTopDown | TreeWalkBottomUp | TreeWalkInorderTopFirstPre 
    | TreeWalkInorderTopLastPre | TreeWalkInorderTopFirstPost | TreeWalkInorderTopLastPost
    -- predefined algorithms
    | AlgorithmW | AlgorithmM 
    -- type inference directives
    | DisableDirectives    
    -- do kind inferencing
    | KindInferencing    
    -- other type inference options
    | RightToLeft | NoSpreading
    | NoRepairHeuristics | UnifierHeuristics | SelectConstraintNumber Int
    | Overloading | SignatureWarnings
    
    deriving Eq

lvmPathFromOptions :: [Option] -> Maybe String
lvmPathFromOptions [] = Nothing
lvmPathFromOptions (LvmPath s : _) = Just s
lvmPathFromOptions (_ : rest) = lvmPathFromOptions rest

selectCNR :: String -> Option
selectCNR s
   | all isDigit s && not (null s) = SelectConstraintNumber (read s) 
   | otherwise                     = SelectConstraintNumber (-1) -- problem with argument 
