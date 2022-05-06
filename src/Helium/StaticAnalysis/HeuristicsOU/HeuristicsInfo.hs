{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-| Module      :  HeuristicsInfo
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Contains instance declarations. he type graph heuristics can be deployed 
	using the additional information that is stored by the Helium compiler for 
	each type constraint
-}

module Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo where

import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.Utils.OneLiner
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Messages.Messages
import Helium.StaticAnalysis.Messages.HeliumMessages (freshenRepresentation)
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.Utils.Utils (internalError)
import Data.Char
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes

class WithHints a where
   addHint          :: String -> String -> a -> a
   addReduction     :: Maybe ReductionTrace -> a -> a
   typeErrorForTerm :: (Bool,Bool) -> Int -> OneLineTree -> MonoType -> (MonoType,MonoType) -> Range -> a -> a
   
instance WithHints ConstraintInfo where
   addHint descr str = addProperty (WithHint (descr, MessageString str))
   addReduction trc ci = case trc of
      Just [] -> ci
      Just xs -> addProperty (WithReduction xs) ci
      Nothing -> ci
   typeErrorForTerm (isInfixApplication,isPatternApplication) argumentNumber termOneLiner functionType (t1, t2) range cinfo =
         let 
            [MType functionType', MType t1', MType t2'] = freshenRepresentation [MType functionType :: RType ConstraintInfo, MType t1, MType t2]
            typeError = TypeError [range] [oneLiner] table []
            oneLiner  = MessageOneLiner (MessageString ("Type error in " ++ location cinfo))
            table     = [ description1     <:> MessageOneLineTree (oneLinerSource source1)
                        , description2     <:> MessageOneLineTree (oneLinerSource source2)
                        , "type"           >:> MessageMonoType functionType'
                        , description3     <:> MessageOneLineTree termOneLiner
                        , "type"           >:> MessageMonoType t1'
                        , "does not match" >:> MessageMonoType t2'
                        ]
            (description1, source1, source2) =
               case convertSources (sources cinfo) of
                  [(d1,s1), (_, s2)] -> (d1, s1, s2)
                  _ -> internalError "ConstraintInfo" "specialApplicationTypeError" "expected two elements in list"
            description2 
               | isPatternApplication   = "constructor"
               | not isInfixApplication = "function"
               | otherwise =  
                     case show (MessageOneLineTree (oneLinerSource source2)) of
                        c:_ | isLower c -> "function"
                           | isUpper c -> "constructor"
                        _               -> "operator"
            description3
               | isInfixApplication = if argumentNumber == 0 then "left operand" else "right operand"
               | otherwise          = ordinal False (argumentNumber + 1) ++ " argument"
         in setTypeError typeError cinfo
    

skip_UHA_FB_RHS :: InfoTree -> InfoTree
skip_UHA_FB_RHS tree = 
   case self (attribute tree) of
      UHA_FB _  -> maybe tree skip_UHA_FB_RHS (parent tree) 
      UHA_RHS _ -> maybe tree skip_UHA_FB_RHS (parent tree)
      _        -> tree
   
findVariableInPat :: Name -> InfoTree -> InfoTree
findVariableInPat name tree = 
   case children tree of
      [] -> tree
      cs -> let p x = case self (attribute x) of
                         UHA_Pat pat -> hasVariable name pat
                         _ -> False
            in case filter p cs of
                  [] -> tree
                  child:_ -> findVariableInPat name child

hasVariable :: Name -> Pattern -> Bool
hasVariable name pattern' =
   case pattern' of
      Pattern_Variable _ n -> name == n
      Pattern_As _ n pat   -> name == n || hasVariable name pat
      Pattern_Parenthesized _ pat -> hasVariable name pat
      Pattern_InfixConstructor _ pat1 _ pat2 -> hasVariable name pat1 || hasVariable name pat2
      Pattern_Constructor _ _ pats -> any (hasVariable name) pats
      Pattern_List _ pats -> any (hasVariable name) pats
      Pattern_Tuple _ pats -> any (hasVariable name) pats
      _ -> False

maybeAddLocation :: UHA_Source -> MessageBlock
maybeAddLocation src
   | match = 
        MessageCompose 
           [ MessageOneLineTree (oneLinerSource src)
           , MessageString " at "
           , MessageRange (rangeOfSource src)
           ]
   | otherwise =  
        MessageOneLineTree (oneLinerSource src)

 where match =
          case src of
             UHA_Expr (Expression_Variable _ _) -> True
             UHA_Pat  (Pattern_Variable _ _)    -> True
             _ -> False
