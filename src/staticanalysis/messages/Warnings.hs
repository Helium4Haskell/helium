-----------------------------------------------------------------------------
-- |The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- Warnings that are reported during static analysis.
-- (the phase before type inference, as well as during type inference)
--
-----------------------------------------------------------------------------

module Warnings where

import UHA_Range    (getNameRange, showRange, sortRanges)
import UHA_Syntax
import UHA_Utils
import Top.Types
import Messages
import Utils        (internalError)
import qualified UHA_Pretty as PP (sem_Pattern, sem_LeftHandSide, sem_Expression)

-------------------------------------------------------------
-- (Static) Warnings

type Warnings = [Warning]
data Warning  = NoTypeDef Name TpScheme Bool
              | Shadow Name Name
              | Unused Entity Name
              | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}
              | MissingPatterns Range (Maybe Name) Tp [[Pattern]] String String
              | UnreachablePatternCase Range Pattern
              | UnreachablePatternLHS  LeftHandSide
              | UnreachableGuard Range Expression
              | FallThrough Range

instance HasMessage Warning where
   getMessage x = [MessageOneLiner (MessageString ("Warning: " ++ showWarning x))]
   getRanges warning = case warning of
      NoTypeDef name _ _            -> [getNameRange name]
      Shadow _ name                 -> [getNameRange name]
      Unused _ name                 -> [getNameRange name]
      SimilarFunctionBindings n1 n2 -> sortRanges [getNameRange n1, getNameRange n2]
      MissingPatterns rng _ _ _ _ _ -> [rng]
      UnreachablePatternCase rng _  -> [rng]
      UnreachableGuard  rng _       -> [rng]
      FallThrough rng               -> [rng]
      UnreachablePatternLHS (LeftHandSide_Function      rng _ _  ) -> [rng]
      UnreachablePatternLHS (LeftHandSide_Infix         rng _ _ _) -> [rng]
      UnreachablePatternLHS (LeftHandSide_Parenthesized rng _ _  ) -> [rng]
      _                             -> internalError "Messages.hs" 
                                                     "instance IsMessage Warning" 
                                                     "unknown type of Warning"

showWarning :: Warning -> String
showWarning warning = case warning of

   NoTypeDef name tpscheme topLevel ->
      "Missing type signature: " ++ showNameAsVariable name ++ " :: " ++ show tpscheme

   Shadow shadowee shadower ->
      "Variable " ++ show (show shadower) ++ " shadows the one at " ++ showRange (getNameRange shadowee)

   Unused entity name ->
      capitalize (show entity) ++ " " ++ show (show name) ++ " is not used"
    
   SimilarFunctionBindings suspect witness ->
      let [n1, n2] = sortNamesByRange [suspect, witness]
      in "Suspicious adjacent functions " ++ (show.show) n1 ++ " and " ++ (show.show) n2

   MissingPatterns _ Nothing tp pss place sym ->
      "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
      ++ concatMap (("\n  " ++).(++ (sym ++ " ...")).concatMap ((++ " ").show.PP.sem_Pattern)) pss
   
   MissingPatterns _ (Just n) tp pss place sym
     | isOperatorName n -> let name = getNameName n in
        "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
        ++ concatMap (\[l, r] -> "\n  " ++ (show.PP.sem_Pattern) l ++ " " ++ name ++ " " ++ (show.PP.sem_Pattern) r ++ " " ++ sym ++ " ...") pss
     | otherwise        -> let name = getNameName n in
        "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
        ++ concatMap (("\n  " ++).(name ++).(' ' :).(++ (sym ++ " ...")).concatMap ((++ " ").show.PP.sem_Pattern)) pss

   UnreachablePatternLHS  lhs -> "Unreachable pattern: " ++ (show.PP.sem_LeftHandSide) lhs
   UnreachablePatternCase _ p -> "Unreachable pattern: " ++ (show.PP.sem_Pattern     ) p

   UnreachableGuard _ e -> "Unreachable guard: | " ++ (show.PP.sem_Expression) e

   FallThrough _ -> "Possible fallthrough"

   _ -> internalError "Messages" "showWarning" "unknown type of Warning"

plural :: [a] -> String -> String
plural [_] = id
plural _   = (++ "s")
