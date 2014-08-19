{-| Module      :  Warnings
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Warnings that are reported during static analysis.
        (the phase before type inference, as well as during type inference)
-}

module Helium.StaticAnalysis.Messages.Warnings where

import Helium.Syntax.UHA_Range    (getNameRange, showRange, sortRanges)
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Top.Types
import Helium.StaticAnalysis.Messages.Messages
import Data.List    (intercalate)
import qualified Helium.Syntax.UHA_Pretty as PP (sem_Pattern, wrap_Pattern, Inh_Pattern (..), Syn_Pattern (..), sem_LeftHandSide, wrap_LeftHandSide, Inh_LeftHandSide (..), Syn_LeftHandSide (..), sem_Expression, wrap_Expression, Inh_Expression (..), Syn_Expression (..))
import qualified Text.PrettyPrint.Leijen as PPrint

-------------------------------------------------------------
-- (Static) Warnings

type Warnings = [Warning]
data Warning  = NoTypeDef Name TpScheme Bool{- toplevel? -} Bool{- simple pat and overloaded? -}
              | Shadow Name Name
              | Unused Entity Name
              | SimilarFunctionBindings Name {- without typesignature -} Name {- with type signature -}
              | SuspiciousTypeVariable Name {- the type variable -} Name {- the type constant -}
              | ReduceContext Range Predicates Predicates
              | MissingPatterns Range (Maybe Name) Tp [[Pattern]] String String
              | UnreachablePatternCase Range Pattern
              | UnreachablePatternLHS  LeftHandSide
              | UnreachableGuard Range Expression
              | FallThrough Range
              | SignatureTooSpecific Name TpScheme TpScheme 
              
instance HasMessage Warning where
   getMessage x = let (oneliner, hints) = showWarning x
                      firstLine = MessageOneLiner (MessageCompose [MessageString "Warning: ", oneliner])
                  in [firstLine, MessageHints "Hint" hints]
   getRanges warning = case warning of
      NoTypeDef name _ _ _          -> [getNameRange name]
      Shadow _ name                 -> [getNameRange name]
      Unused _ name                 -> [getNameRange name]
      SimilarFunctionBindings n1 n2 -> sortRanges [getNameRange n1, getNameRange n2]
      SuspiciousTypeVariable name _ -> [getNameRange name]
      ReduceContext rng _ _         -> [rng]
      MissingPatterns rng _ _ _ _ _ -> [rng]
      UnreachablePatternCase rng _  -> [rng]
      UnreachableGuard  rng _       -> [rng]
      FallThrough rng               -> [rng]
      UnreachablePatternLHS (LeftHandSide_Function      rng _ _  ) -> [rng]
      UnreachablePatternLHS (LeftHandSide_Infix         rng _ _ _) -> [rng]
      UnreachablePatternLHS (LeftHandSide_Parenthesized rng _ _  ) -> [rng]
      SignatureTooSpecific name _ _ -> [getNameRange name]

showWarning :: Warning -> (MessageBlock {- oneliner -}, MessageBlocks {- hints -})
showWarning warning = case warning of

   NoTypeDef name tpscheme _ simplePat ->
      ( MessageString ("Missing type signature: " ++ showNameAsVariable name ++ " :: " ++ show tpscheme)
      , let hint = "Because " ++ showNameAsVariable name ++ " has an overloaded type, computations may be repeated. " ++
                   "Insert the missing type signature if this is indeed your intention."
        in [ MessageString hint | simplePat ]
      )

   Shadow shadowee shadower ->
      ( MessageString ("Variable " ++ show (show shadower) ++ " shadows the one at " ++ showRange (getNameRange shadowee))
      , []
      )

   Unused entity name ->
      ( MessageString (capitalize (show entity) ++ " " ++ show (show name) ++ " is not used")
      , []
      )

   SimilarFunctionBindings suspect witness ->
      ( let [n1, n2] = sortNamesByRange [suspect, witness]
        in MessageString ("Suspicious adjacent functions " ++ (show.show) n1 ++ " and " ++ (show.show) n2)
      , []
      )

   SuspiciousTypeVariable varName conName ->
      ( MessageString ("Suspicious type variable " ++ (show.show) varName)
      , [ MessageString ("Did you mean the type constructor " ++ (show.show) conName ++ " ?") ]
      )

   ReduceContext _ predicates reduced ->
      let showPredicates ps = "(" ++ intercalate ", " (map show ps) ++ ")"  
      in ( MessageString ( "The context " ++ showPredicates predicates ++ " has superfluous predicates." )
         , [ MessageString ("You may change it into " ++ showPredicates reduced ++ ".") ]
         )

   
   MissingPatterns _ Nothing _ pss place sym ->
      let text   = "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
                   ++ concatMap (("\n  " ++).(++ (sym ++ " ...")).concatMap ((++ " ").show.semP)) pss
      in (MessageString text, [])
   
   MissingPatterns _ (Just n) _ pss place sym
     | isOperatorName n -> 
          let name = getNameName n 
              text = "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
                     ++ concatMap (\[l, r] -> "\n  " ++ (show.semP) l ++ " " ++ name ++ " " 
                     ++ (show.semP) r ++ " " ++ sym ++ " ...") pss
          in (MessageString text, [])
          
     | otherwise -> 
          let name = getNameName n
              text =  "Missing " ++ plural pss "pattern" ++ " in " ++ place ++ ": "
                      ++ concatMap (("\n  " ++).(name ++).(' ' :).(++ (sym ++ " ...")).concatMap ((++ " ").show.semP)) pss
          in (MessageString text, [])

   UnreachablePatternLHS  lhs -> 
      ( MessageString ("Unreachable pattern: " ++ show (PP.text_Syn_LeftHandSide (PP.wrap_LeftHandSide (PP.sem_LeftHandSide lhs) PP.Inh_LeftHandSide)))
      , []
      )
   
   UnreachablePatternCase _ p -> 
      ( MessageString ("Unreachable pattern: " ++ (show.semP ) p)
      , []
      )

   UnreachableGuard _ e -> 
      ( MessageString ("Unreachable guard: | " ++ show (PP.text_Syn_Expression (PP.wrap_Expression (PP.sem_Expression e) PP.Inh_Expression)))
      , []
      )

   FallThrough _ -> 
      ( MessageString "It is good practise to have 'otherwise' as the last guard"
      , []
      )

   SignatureTooSpecific name signature scheme -> 
      ( MessageCompose 
           [ MessageString (
                "Declared type signature for "++show (show name)++" could be more general\n"++
                "   declared type : ")
           , MessageType signature
           , MessageString ('\n' : "   inferred type : ")
           , MessageType scheme
           ]
      , []
      )

plural :: [a] -> String -> String
plural [_] = id
plural _   = (++ "s")

semP :: Pattern -> PPrint.Doc
semP p = PP.text_Syn_Pattern (PP.wrap_Pattern (PP.sem_Pattern p) PP.Inh_Pattern)
