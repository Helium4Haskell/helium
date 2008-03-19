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
    , loggerDEFAULTHOST
    , loggerDEFAULTPORT
    , hostNameFromOptions
    , portNrFromOptions
    ) where

import System
import Version
import Data.Char
import Monad(when)
import System.Console.GetOpt

loggerDEFAULTHOST :: String
loggerDEFAULTHOST = "localhost"

loggerDEFAULTPORT :: Int
loggerDEFAULTPORT = 5010

unwordsBy :: String -> [String] -> String
unwordsBy sep [] = ""
unwordsBy sep [w] = w
unwordsBy sep (w:ws) = w ++ sep ++ unwordsBy sep ws

-- Keep only the last of the overloading flags and the last of the logging enable flags.
-- The alert flag overrides logging turned off.
-- This function also collects all -P flags together and merges them into one. The order of the
-- directories is the order in which they were specified.
-- Adds Overloading flag to make sure that this is the default.
simplifyOptions :: [Option] -> [Option]
simplifyOptions ops = 
    let
      revdefops = reverse (DisableLogging : (Overloading : ops)) -- Add defaults that will be ignored if explicit flags are present
      modops    = if (AlertLogging `elem` revdefops) 
                  then EnableLogging : revdefops -- Explicitly enable logging as well, just to be safe
                  else revdefops
    in
      collectPaths (keepFirst [Overloading, NoOverloading] (keepFirst [EnableLogging, DisableLogging] modops)) [] []
          where
            -- Assumes the options are in reverse order, and also reverses them.
            -- Collects several LvmPath options into one
            collectPaths [] paths newops       = LvmPath (unwordsBy ":" paths) : newops              
            collectPaths (LvmPath path : rest) paths newops
                                               = collectPaths rest (path : paths) newops
            collectPaths (opt : rest) paths newops
                                               = collectPaths rest paths (opt : newops)                                   
            keepFirst fromList []              = []
            keepFirst fromList (opt : rest)    = if (opt `elem` fromList) then
                                                   opt : optionFilter fromList rest
                                                 else
                                                   opt : keepFirst fromList rest
            optionFilter fromList []           = []
            optionFilter fromList (opt : rest) = if (opt `elem` fromList) then
                                                   optionFilter fromList rest
                                                 else
                                                   opt : optionFilter fromList rest

processArgs :: [String] -> IO ([Option], String)
processArgs args =
    let (options, arguments, errors) = getOpt Permute (optionDescription True True) args
        moreOptions         = MoreOptions `elem` options || experimentalOptions
        experimentalOptions = ExperimentalOptions `elem` options
    in if not (null errors) || length arguments /= 1 then do
        putStrLn $ "Helium compiler " ++ version
        putStrLn (usageInfo "Usage: helium [options] file" (optionDescription moreOptions experimentalOptions))
        exitWith (ExitFailure 1)
    else
        do 
          let simpleOptions = simplifyOptions options
          when (Verbose `elem` simpleOptions) $
            putStrLn ("Options after simplification: " ++ (show simpleOptions)++"\n")
          return (simpleOptions, (head arguments))
 where
   optionDescription moreOptions experimentalOptions =
      -- Main options
      [ Option "b" ["build"]                (NoArg BuildOne) "recompile module even if up to date"
      , Option "B" ["build-all"]            (NoArg BuildAll) "recompile all modules even if up to date"
      , Option "i" ["dump-information"]     (NoArg DumpInformationForThisModule) "show information about this module"
      , Option "I" ["dump-all-information"] (NoArg DumpInformationForAllModules) "show information about all imported modules"
      , Option ""  ["enable-logging"]       (NoArg EnableLogging) "enable logging, overrides previous disable-logging"
      , Option ""  ["disable-logging"]      (NoArg DisableLogging) "disable logging (default), overrides previous enable-logging flags"
      , Option "a" ["alert"]                (NoArg AlertLogging) "compiles with alert flag in logging, overrides all disable-logging flags"
      , Option ""  ["overloading"]          (NoArg Overloading) "turn overloading on (default), overrides all previous no-overloading flags"
      , Option ""  ["no-overloading"]       (NoArg NoOverloading) "turn overloading off, overrides all previous overloading flags"
      , Option "P" ["lvmpath"]              (ReqArg LvmPath "PATH") "use PATH as search path"
      , Option "v" ["verbose"]              (NoArg Verbose) "show the phase the compiler is in"
      , Option "w" ["no-warnings"]          (NoArg NoWarnings) "do not show warnings"
      , Option "X" ["more-options"]         (NoArg MoreOptions) "show more compiler options"
      , Option ""  ["info"]                 (ReqArg Information "NAME") "display information about NAME"
      
      ]
      ++
      -- More options
      if not moreOptions then [] else
      [ Option "1" ["stop-after-parsing"]          (NoArg StopAfterParser) "stop after parsing"
      , Option "2" ["stop-after-static-analysis"]  (NoArg StopAfterStaticAnalysis) "stop after static analysis"
      , Option "3" ["stop-after-type-inferencing"] (NoArg StopAfterTypeInferencing) "stop after type inferencing"
      , Option "4" ["stop-after-desugaring"]       (NoArg StopAfterDesugar) "stop after desugaring into Core"    
      , Option "t" ["dump-tokens"]                 (NoArg DumpTokens) "dump tokens to screen"
      , Option "u" ["dump-uha"]                    (NoArg DumpUHA) "pretty print abstract syntax tree"
      , Option "c" ["dump-core"]                   (NoArg DumpCore) "pretty print Core program"
      , Option "C" ["save-core"]                   (NoArg DumpCoreToFile) "write Core program to file"
      , Option ""  ["debug-logger"]                (NoArg DebugLogger) "show logger debug information"
      , Option ""  ["hostname"]                    (ReqArg HostName "HOST") ("specify which HOST to use for logging (default " ++ loggerDEFAULTHOST ++ ")")
      , Option ""  ["portnumber"]                  (ReqArg selectPortNr "PORT") ("select the PORT number for the logger (default: " ++ show loggerDEFAULTPORT ++ ")")
      , Option "d" ["type-debug"]                  (NoArg DumpTypeDebug) "debug constraint-based type inference"         
      , Option "W" ["algorithm-w"]                 (NoArg AlgorithmW) "use bottom-up type inference algorithm W"
      , Option "M" ["algorithm-m"]                 (NoArg AlgorithmM) "use folklore top-down type inference algorithm M"
      , Option ""  ["no-directives" ]              (NoArg DisableDirectives) "disable type inference directives"
      , Option ""  ["no-repair-heuristics"]        (NoArg NoRepairHeuristics) "don't suggest program fixes"
      ]
      ++
      -- Experimental options
      if not experimentalOptions then [] else
      [ Option "" ["experimental-options"] (NoArg ExperimentalOptions) "show experimental compiler options"
      , Option "" ["kind-inferencing"]     (NoArg KindInferencing) "perform kind inference (experimental)"
      , Option "" ["signature-warnings"]   (NoArg SignatureWarnings) "warn for too specific signatures (experimental)" 
      , Option "" ["right-to-left"]        (NoArg RightToLeft) "right-to-left treewalk"
      , Option "" ["no-spreading" ]        (NoArg NoSpreading) "do not spread type constraints (experimental)"
      , Option "" ["treewalk-topdown" ]    (NoArg TreeWalkTopDown) "top-down treewalk"
      , Option "" ["treewalk-bottomup"]    (NoArg TreeWalkBottomUp) "bottom up-treewalk"
      , Option "" ["treewalk-inorder1"]    (NoArg TreeWalkInorderTopFirstPre) "treewalk (top;upward;child)"
      , Option "" ["treewalk-inorder2"]    (NoArg TreeWalkInorderTopLastPre) "treewalk (upward;child;top)"
      , Option "" ["treewalk-inorder3"]    (NoArg TreeWalkInorderTopFirstPost) "treewalk (top;child;upward)"
      , Option "" ["treewalk-inorder4"]    (NoArg TreeWalkInorderTopLastPost) "treewalk (child;upward;top)"
      , Option "" ["solver-simple"     ]   (NoArg SolverSimple) "a simple constraint solver"
      , Option "" ["solver-greedy"     ]   (NoArg SolverGreedy) "a fast constraint solver"
      , Option "" ["solver-typegraph"  ]   (NoArg SolverTypeGraph) "type graph constraint solver"
      , Option "" ["solver-combination"]   (NoArg SolverCombination) "switches between \"greedy\" and \"type graph\""
      , Option "" ["solver-chunks"     ]   (NoArg SolverChunks) "solves chunks of constraints (default)"
      , Option "" ["unifier-heuristics"]   (NoArg UnifierHeuristics)  "use unifier heuristics (experimental)"
      , Option "" ["select-cnr"]           (ReqArg selectCNR "CNR") "select constraint number to be reported"
      ]

data Option 
   -- Main options
   = BuildOne | BuildAll | DumpInformationForThisModule | DumpInformationForAllModules
   | DisableLogging | EnableLogging | AlertLogging | Overloading | NoOverloading | LvmPath String | Verbose | NoWarnings | MoreOptions
   | Information String
   -- More options
   | StopAfterParser | StopAfterStaticAnalysis | StopAfterTypeInferencing | StopAfterDesugar
   | DumpTokens | DumpUHA | DumpCore | DumpCoreToFile 
   | DebugLogger | HostName String | PortNr Int 
   | DumpTypeDebug | AlgorithmW | AlgorithmM | DisableDirectives | NoRepairHeuristics
   -- Experimental options
   | ExperimentalOptions |KindInferencing | SignatureWarnings | RightToLeft | NoSpreading
   | TreeWalkTopDown | TreeWalkBottomUp | TreeWalkInorderTopFirstPre | TreeWalkInorderTopLastPre
   | TreeWalkInorderTopFirstPost | TreeWalkInorderTopLastPost | SolverSimple | SolverGreedy
   | SolverTypeGraph | SolverCombination | SolverChunks | UnifierHeuristics
   | SelectConstraintNumber Int
 deriving (Eq, Show)

lvmPathFromOptions :: [Option] -> Maybe String
lvmPathFromOptions [] = Nothing
lvmPathFromOptions (LvmPath s : _) = Just s
lvmPathFromOptions (_ : rest) = lvmPathFromOptions rest


-- Takes the first in the list. Better to remove duplicates!
hostNameFromOptions :: [Option] -> Maybe String
hostNameFromOptions [] = Nothing
hostNameFromOptions (HostName s : _) = Just s
hostNameFromOptions (_ : rest) = hostNameFromOptions rest

-- Takes the first in the list. Better to remove duplicates!
portNrFromOptions :: [Option] -> Maybe Int
portNrFromOptions [] = Nothing
portNrFromOptions (PortNr pn: _) = Just pn
portNrFromOptions (_ : rest) = portNrFromOptions rest

selectPortNr :: String -> Option
selectPortNr pn 
   | all isDigit pn = PortNr (read ('0':pn)) 
   | otherwise     = PortNr (-1) -- problem with argument
   
selectCNR :: String -> Option
selectCNR s
   | all isDigit s = SelectConstraintNumber (read ('0':s)) 
   | otherwise     = SelectConstraintNumber (-1) -- problem with argument
