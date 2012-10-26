{-| Module      :  Args
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

-}

module Main.Args
    ( Option(..)
    , processHeliumArgs
    , processTexthintArgs
    , lvmPathFromOptions
    , loggerDEFAULTHOST
    , simplifyOptions
    , argsToOptions
    , loggerDEFAULTPORT
    , hostFromOptions
    , portFromOptions
    , hasAlertOption
    ) where

import System.Environment
import System.Exit
import Main.Version
import Data.Maybe
import Control.Monad(when)
import System.Console.GetOpt
import Data.Char

loggerDEFAULTHOST :: String
loggerDEFAULTHOST = "helium.zoo.cs.uu.nl"

loggerDEFAULTPORT :: Int
loggerDEFAULTPORT = 5010

unwordsBy :: String -> [String] -> String
unwordsBy _   [] = ""
unwordsBy _   [w] = w
unwordsBy sep (w:ws) = w ++ sep ++ unwordsBy sep ws

-- Keep only the last of the overloading flags and the last of the logging enable flags.
-- The alert flag overrides logging turned off.
-- This function also collects all -P flags together and merges them into one. The order of the
-- directories is the order in which they were specified.
simplifyOptions :: [Option] -> [Option]
simplifyOptions ops =
    let
      revdefops = reverse ops
      modops    = case alertMessageFromOptions revdefops of
                    (Just _)  ->  EnableLogging : revdefops -- Explicitly enable logging as well, just to be safe
                    Nothing   ->  revdefops
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
            keepFirst _        []              = []
            keepFirst fromList (opt : rest)    = if (opt `elem` fromList) then
                                                   opt : optionFilter fromList rest
                                                 else
                                                   opt : keepFirst fromList rest
            optionFilter _        []           = []
            optionFilter fromList (opt : rest) = if (opt `elem` fromList) then
                                                   optionFilter fromList rest
                                                 else
                                                   opt : optionFilter fromList rest

terminateWithMessage :: [Option] -> String -> [String] -> IO ([Option], Maybe String)
terminateWithMessage options message errors = do
    let experimentalOptions = ExperimentalOptions `elem` options
    let moreOptions         = MoreOptions `elem` options || experimentalOptions
    putStrLn message
    putStrLn (unlines errors)
    putStrLn $ "Helium compiler " ++ version
    putStrLn (usageInfo "Usage: helium [options] file [options]" (optionDescription moreOptions experimentalOptions))
    exitWith (ExitFailure 1)

processTexthintArgs :: [String] -> IO ([Option], Maybe String)
processTexthintArgs = basicProcessArgs []

processHeliumArgs :: [String] -> IO ([Option], Maybe String)
processHeliumArgs args = do
    (options, maybeFiles) <- basicProcessArgs [DisableLogging, Overloading] args
    case maybeFiles of
        Nothing ->
          terminateWithMessage options "Error in invocation: the name of the module to be compiled seems to be missing." []
        Just _ ->
          return (options, maybeFiles)

-- Sometimes you know the options are correct. Then you can use this.
argsToOptions args =
    let
      (opts,_,_) = getOpt Permute (optionDescription True True) args
    in
      opts

-- The Maybe String indicates that a file may be missing
basicProcessArgs :: [Option] -> [String] ->  IO ([Option], Maybe String)
basicProcessArgs defaults args =
    let (options, arguments, errors) = getOpt Permute (optionDescription True True) args
    in if not (null errors) then do
          terminateWithMessage options "Error in invocation: list of parameters is erroneous.\nProblem(s):"
                               (map ("  " ++) errors)
    else
        if (length arguments > 1) then
            terminateWithMessage options ("Error in invocation: only one non-option parameter expected, but found instead:\n" ++ (unlines (map ("  "++) arguments))) []
        else
            do
              let simpleOptions = simplifyOptions (defaults ++ options)
              when (Verbose `elem` simpleOptions) $
                putStrLn ("Options after simplification: " ++ (show simpleOptions)++"\n")
              let argument = if null arguments then Nothing else Just (head arguments)
              return (simpleOptions, argument)

optionDescription moreOptions experimentalOptions =
      -- Main options
      [ Option "b" [flag BuildOne]                      (NoArg BuildOne) "recompile module even if up to date"
      , Option "B" [flag BuildAll]                      (NoArg BuildAll) "recompile all modules even if up to date"
      , Option "i" [flag DumpInformationForThisModule]  (NoArg DumpInformationForThisModule) "show information about this module"
      , Option "I" [flag DumpInformationForAllModules]  (NoArg DumpInformationForAllModules) "show information about all imported modules"
      , Option ""  [flag EnableLogging]                 (NoArg EnableLogging) "enable logging, overrides previous disable-logging"
      , Option ""  [flag DisableLogging]                (NoArg DisableLogging) "disable logging (default), overrides previous enable-logging flags"
      , Option "a" [flag (Alert "")]                   (ReqArg Alert "MESSAGE") "compiles with alert flag in logging; MESSAGE specifies the reason for the alert."
      , Option ""  [flag Overloading]                   (NoArg Overloading) "turn overloading on (default), overrides all previous no-overloading flags"
      , Option ""  [flag NoOverloading]                 (NoArg NoOverloading) "turn overloading off, overrides all previous overloading flags"
      , Option "P" [flag (LvmPath "")]                 (ReqArg LvmPath "PATH") "use PATH as search path"
      , Option "v" [flag Verbose]                       (NoArg Verbose) "show the phase the compiler is in"
      , Option "w" [flag NoWarnings]                    (NoArg NoWarnings) "do notflag warnings"
      , Option "X" [flag MoreOptions]                   (NoArg MoreOptions) "show more compiler options"
      , Option ""  [flag (Information "")]             (ReqArg Information "NAME") "display information about NAME"

      ]
      ++
      -- More options
      if not moreOptions then [] else
      [ Option "1" [flag StopAfterParser]               (NoArg StopAfterParser) "stop after parsing"
      , Option "2" [flag StopAfterStaticAnalysis]       (NoArg StopAfterStaticAnalysis) "stop after static analysis"
      , Option "3" [flag StopAfterTypeInferencing]      (NoArg StopAfterTypeInferencing) "stop after type inferencing"
      , Option "4" [flag StopAfterDesugar]              (NoArg StopAfterDesugar) "stop after desugaring into Core"
      , Option "t" [flag DumpTokens]                    (NoArg DumpTokens) "dump tokens to screen"
      , Option "u" [flag DumpUHA]                       (NoArg DumpUHA) "pretty print abstract syntax tree"
      , Option "c" [flag DumpCore]                      (NoArg DumpCore) "pretty print Core program"
      , Option "C" [flag DumpCoreToFile]                (NoArg DumpCoreToFile) "write Core program to file"
      , Option ""  [flag DebugLogger]                   (NoArg DebugLogger) "show logger debug information"
      , Option ""  [flag (Host "")]                     (ReqArg Host "HOST") ("specify which HOST to use for logging (default " ++ loggerDEFAULTHOST ++ ")")
      , Option ""  [flag (Port 0)]                      (ReqArg selectPort "PORT") ("select the PORT number for the logger (default: " ++ show loggerDEFAULTPORT ++ ")")
      , Option "d" [flag DumpTypeDebug]                 (NoArg DumpTypeDebug) "debug constraint-based type inference"
      , Option "W" [flag AlgorithmW]                    (NoArg AlgorithmW) "use bottom-up type inference algorithm W"
      , Option "M" [flag AlgorithmM ]                   (NoArg AlgorithmM) "use folklore top-down type inference algorithm M"
      , Option ""  [flag DisableDirectives]             (NoArg DisableDirectives) "disable type inference directives"
      , Option ""  [flag NoRepairHeuristics]            (NoArg NoRepairHeuristics) "don't suggest program fixes"
      , Option ""  [flag HFullQualification]             (NoArg HFullQualification) "to determine fully qualified names for Holmes"
      ]
      ++
      -- Experimental options
      if not experimentalOptions then [] else
      [ Option "" [flag ExperimentalOptions]            (NoArg ExperimentalOptions) "show experimental compiler options"
      , Option "" [flag KindInferencing]                (NoArg KindInferencing) "perform kind inference (experimental)"
      , Option "" [flag SignatureWarnings]              (NoArg SignatureWarnings) "warn for too specific signatures (experimental)"
      , Option "" [flag RightToLeft]                    (NoArg RightToLeft) "right-to-left treewalk"
      , Option "" [flag NoSpreading]                    (NoArg NoSpreading) "do not spread type constraints (experimental)"
      , Option "" [flag TreeWalkTopDown]                (NoArg TreeWalkTopDown) "top-down treewalk"
      , Option "" [flag TreeWalkBottomUp]               (NoArg TreeWalkBottomUp) "bottom up-treewalk"
      , Option "" [flag TreeWalkInorderTopFirstPre]     (NoArg TreeWalkInorderTopFirstPre) "treewalk (top;upward;child)"
      , Option "" [flag TreeWalkInorderTopLastPre]      (NoArg TreeWalkInorderTopLastPre) "treewalk (upward;child;top)"
      , Option "" [flag TreeWalkInorderTopFirstPost]    (NoArg TreeWalkInorderTopFirstPost) "treewalk (top;child;upward)"
      , Option "" [flag TreeWalkInorderTopLastPost]     (NoArg TreeWalkInorderTopLastPost) "treewalk (child;upward;top)"
      , Option "" [flag SolverSimple]                   (NoArg SolverSimple) "a simple constraint solver"
      , Option "" [flag SolverGreedy]                   (NoArg SolverGreedy) "a fast constraint solver"
      , Option "" [flag SolverTypeGraph]                (NoArg SolverTypeGraph) "type graph constraint solver"
      , Option "" [flag SolverCombination]              (NoArg SolverCombination) "switches between \"greedy\" and \"type graph\""
      , Option "" [flag SolverChunks]                   (NoArg SolverChunks) "solves chunks of constraints (default)"
      , Option "" [flag UnifierHeuristics]              (NoArg UnifierHeuristics)  "use unifier heuristics (experimental)"
      , Option "" [flag (SelectConstraintNumber 0)]     (ReqArg selectCNR "CNR") "select constraint number to be reported"
      , Option "" [flag NoOverloadingTypeCheck]         (NoArg NoOverloadingTypeCheck)  "disable overloading errors (experimental)"
      , Option "" [flag NoPrelude]                      (NoArg NoPrelude)  "do not import the prelude (experimental)"
      ]


data Option
   -- Main options
   = BuildOne | BuildAll | DumpInformationForThisModule | DumpInformationForAllModules
   | DisableLogging | EnableLogging | Alert String | Overloading | NoOverloading | LvmPath String | Verbose | NoWarnings | MoreOptions
   | Information String
   -- More options
   | StopAfterParser | StopAfterStaticAnalysis | StopAfterTypeInferencing | StopAfterDesugar
   | DumpTokens | DumpUHA | DumpCore | DumpCoreToFile
   | DebugLogger | Host String | Port Int
   | DumpTypeDebug | AlgorithmW | AlgorithmM | DisableDirectives | NoRepairHeuristics | HFullQualification
   -- Experimental options
   | ExperimentalOptions | KindInferencing | SignatureWarnings | RightToLeft | NoSpreading
   | TreeWalkTopDown | TreeWalkBottomUp | TreeWalkInorderTopFirstPre | TreeWalkInorderTopLastPre
   | TreeWalkInorderTopFirstPost | TreeWalkInorderTopLastPost | SolverSimple | SolverGreedy
   | SolverTypeGraph | SolverCombination | SolverChunks | UnifierHeuristics
   | SelectConstraintNumber Int | NoOverloadingTypeCheck | NoPrelude | UseTutor
 deriving (Eq)

stripShow :: String -> String
stripShow name = tail (tail (takeWhile ('=' /=) name))

flag = stripShow . show

instance Show Option where
 show BuildOne                           = "--build"
 show BuildAll                           = "--build-all"
 show DumpInformationForThisModule       = "--dump-information"
 show DumpInformationForAllModules       = "--dump-all-information"
 show EnableLogging                      = "--enable-logging"
 show DisableLogging                     = "--disable-logging"
 show (Alert str)                        = "--alert=\"" ++ str ++ "\"" -- May contain spaces
 show Overloading                        = "--overloading"
 show NoOverloading                      = "--no-overloading"
 show (LvmPath str)                      = "--lvmpath=\"" ++ str ++ "\"" -- May contain spaces
 show Verbose                            = "--verbose"
 show NoWarnings                         = "--no-warnings"
 show MoreOptions                        = "--moreoptions"
 show (Information str)                  = "--info=" ++ str
 show StopAfterParser                    = "--stop-after-parsing"
 show StopAfterStaticAnalysis            = "--stop-after-static-analysis"
 show StopAfterTypeInferencing           = "--stop-after-type-inferencing"
 show StopAfterDesugar                   = "--stop-after-desugaring"
 show DumpTokens                         = "--dump-tokens"
 show DumpUHA                            = "--dump-uha"
 show DumpCore                           = "--dump-core"
 show DumpCoreToFile                     = "--save-core"
 show DebugLogger                        = "--debug-logger"
 show (Host host)                        = "--host=" ++ host
 show (Port port)                        = "--port=" ++ (show port)
 show DumpTypeDebug                      = "--type-debug"
 show AlgorithmW                         = "--algorithm-w"
 show AlgorithmM                         = "--algorithm-m"
 show DisableDirectives                  = "--no-directives"
 show NoRepairHeuristics                 = "--no-repair-heuristics"
 show ExperimentalOptions                = "--experimental-options"
 show KindInferencing                    = "--kind-inferencing"
 show SignatureWarnings                  = "--signature-warnings"
 show RightToLeft                        = "--right-to-left"
 show NoSpreading                        = "--no-spreading"
 show TreeWalkTopDown                    = "--treewalk-topdown"
 show TreeWalkBottomUp                   = "--treewalk-bottomup"
 show TreeWalkInorderTopFirstPre         = "--treewalk-inorder1"
 show TreeWalkInorderTopLastPre          = "--treewalk-inorder2"
 show TreeWalkInorderTopFirstPost        = "--treewalk-inorder3"
 show TreeWalkInorderTopLastPost         = "--treewalk-inorder4"
 show SolverSimple                       = "--solver-simple"
 show SolverGreedy                       = "--solver-greedy"
 show SolverTypeGraph                    = "--solver-typegraph"
 show SolverCombination                  = "--solver-combination"
 show SolverChunks                       = "--solver-chunks"
 show UnifierHeuristics                  = "--unifier-heuristics"
 show (SelectConstraintNumber cnr)       = "--select-cnr=" ++ (show cnr)
 show HFullQualification                 = "--H-fullqualification"
 show NoOverloadingTypeCheck             = "--no-overloading-typecheck"
 show NoPrelude                          = "--no-prelude"
 show UseTutor                           = "--use-tutor"


lvmPathFromOptions :: [Option] -> Maybe String
lvmPathFromOptions [] = Nothing
lvmPathFromOptions (LvmPath s : _) = Just s
lvmPathFromOptions (_ : rest) = lvmPathFromOptions rest


-- Takes the first in the list. Better to remove duplicates!
hostFromOptions :: [Option] -> Maybe String
hostFromOptions [] = Nothing
hostFromOptions (Host s : _) = Just s
hostFromOptions (_ : rest) = hostFromOptions rest

-- Takes the first in the list. Better to remove duplicates!
portFromOptions :: [Option] -> Maybe Int
portFromOptions [] = Nothing
portFromOptions (Port pn: _) = Just pn
portFromOptions (_ : rest) = portFromOptions rest

-- Extracts the alert message. Returns Nothing if such is not present.
alertMessageFromOptions :: [Option] -> Maybe String
alertMessageFromOptions [] = Nothing
alertMessageFromOptions (Alert message: _) = Just message
alertMessageFromOptions (_ : rest) = alertMessageFromOptions rest

hasAlertOption :: [Option] -> Bool
hasAlertOption = isJust . alertMessageFromOptions

selectPort :: String -> Option
selectPort pn
   | all isDigit pn = Port (read ('0':pn))
   | otherwise     = Port (-1) -- problem with argument

selectCNR :: String -> Option
selectCNR s
   | all isDigit s = SelectConstraintNumber (read ('0':s))
   | otherwise     = SelectConstraintNumber (-1) -- problem with argument

