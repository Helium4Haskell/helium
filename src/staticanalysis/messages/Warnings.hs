-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Warnings.hs : ...
-- 
-------------------------------------------------------------------------------

module Warnings where

import UHA_Range    (getNameRange, showRange, sortRanges)
import UHA_Syntax
import UHA_Utils    --(showNameAsVariable)
import Types
import Messages
import Utils        (internalError)
import qualified PrettyPrinting (sem_Pattern, sem_LeftHandSide)

-------------------------------------------------------------
-- (Static) Warnings

type Warnings = [Warning]
data Warning  = NoTypeDef Name TpScheme Bool
              | Shadow Name Name
              | Unused Entity Name {- toplevel or not -} Bool
              | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}
              | General Range String -- Maarten
              | MissingPatternsCase Range      Tp  [Pattern]
              | MissingPatternsLHS  Range Name Tp [[Pattern]]
              | UnreachablePatternCase Range Pattern
              | UnreachablePatternLHS  LeftHandSide

general :: String -> Warning
general = General $ Range_Range Position_Unknown Position_Unknown

instance HasMessage Warning where
   getMessage x = [MessageOneLiner (MessageString ("Warning: " ++ showWarning x))]
   getRanges warning = case warning of
      NoTypeDef name _ _            -> [getNameRange name]
      Shadow _ name                 -> [getNameRange name]
      Unused _ name _               -> [getNameRange name]
      SimilarFunctionBindings n1 n2 -> sortRanges [getNameRange n1, getNameRange n2]
      General rng _                 -> [rng]
      MissingPatternsCase rng _ _   -> [rng]
      MissingPatternsLHS  rng _ _ _ -> [rng]
      UnreachablePatternLHS  (LeftHandSide_Function      rng _ _  ) -> [rng]
      UnreachablePatternLHS  (LeftHandSide_Infix         rng _ _ _) -> [rng]
      UnreachablePatternLHS  (LeftHandSide_Parenthesized rng _ _  ) -> [rng]
      UnreachablePatternCase rng _  -> [rng]
      _                             -> internalError "Messages.hs" 
                                                     "instance IsMessage Warning" 
                                                     "unknown type of Warning"

showWarning :: Warning -> String
showWarning warning = case warning of

   NoTypeDef name tpscheme topLevel ->
      "Missing type signature: " ++ showNameAsVariable name ++ " :: " ++ show tpscheme

   Shadow shadowee shadower ->
      "Variable " ++ show (show shadower) ++ " shadows the one at " ++ showRange (getNameRange shadowee)

   Unused entity name toplevel ->
      capitalize (show entity) ++ " " ++ show (show name) ++ " is not used"
    
   SimilarFunctionBindings suspect witness ->
      let [n1, n2] = sortNamesByRange [suspect, witness]
      in "Suspicious adjacent functions " ++ (show.show) n1 ++ " and " ++ (show.show) n2

   General _ warning -> warning
   
   MissingPatternsCase _ tp ps ->
      "Some case-patterns are missing here: "
      ++ show tp
      ++ concatMap (('\n' :).show) (map PrettyPrinting.sem_Pattern ps)

   MissingPatternsLHS _ n tp pss 
     | isOperatorName n -> let name = getNameName n in
        "Some lhs-patterns are missing here: "
        ++ show tp
        ++ concatMap (\[l, r] -> '\n' : (show.PrettyPrinting.sem_Pattern) l ++ " " ++ name ++ " " ++ (show.PrettyPrinting.sem_Pattern) r) pss
     | otherwise        -> let name = getNameName n in
        "Some lhs-patterns are missing here: "
        ++ show tp
        ++ concatMap (('\n' :).(name ++).(' ' :).concatMap ((++ " ").show.PrettyPrinting.sem_Pattern)) pss

   UnreachablePatternLHS  lhs -> "Unreachable pattern: " ++ (show.PrettyPrinting.sem_LeftHandSide) lhs
   UnreachablePatternCase _ p -> "Unreachable pattern: " ++ (show.PrettyPrinting.sem_Pattern     ) p

   _ -> internalError "Messages" "showWarning" "unknown type of Warning"
   

makeUnused :: Entity -> Names -> Bool -> [Warning]
makeUnused entity names toplevel = [ Unused entity name toplevel | name <- names ]   
