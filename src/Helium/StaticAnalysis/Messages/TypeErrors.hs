{-| Module      :  TypeErrors
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Errors that are constructed during type inferece.
-}

module Helium.StaticAnalysis.Messages.TypeErrors where

import Helium.StaticAnalysis.Messages.Messages
import Top.Types

import Helium.Syntax.UHA_Syntax (Range, Name)
import Helium.Syntax.UHA_Range  (getNameRange)
import Helium.Syntax.UHA_Utils
import Helium.StaticAnalysis.Miscellaneous.UHA_Source

import Data.Maybe
import Data.List

type TypeErrors = [TypeError]
data TypeError  = TypeError
                     [Range]                                -- range(s) of the error
                     [MessageLine]                          -- oneliner messages
                     [(Bool, MessageBlock, MessageBlock)]   -- Hugs-like table
                     [TypeErrorHint]                        -- extra hints
     
type TypeErrorHint  = (String, MessageBlock)

instance HasMessage TypeError where
   getMessage (TypeError _ oneliners table hints) =
      let emptyLine  = MessageOneLiner (MessageString "")
          maybeTable | null table = [] 
                     | otherwise  = [ MessageTable (table ++ map (uncurry (<:>)) hints) ]
      in oneliners ++ maybeTable ++ [emptyLine]
   getRanges (TypeError ranges _ _ _) = ranges

instance Substitutable TypeError where
   sub |-> (TypeError ranges oneliner table hints) =
      let table' = [ (b, sub |-> mb1, sub |-> mb2) | (b, mb1, mb2) <- table ] 
          hints' = [ (s, sub |-> mb) | (s, mb) <- hints ]
      in TypeError ranges (sub |-> oneliner) table' hints'
   ftv (TypeError _ oneliner table hints) =
      ftv oneliner `union` ftv [ [mb1, mb2] | (_, mb1, mb2) <- table ] `union` ftv (map snd hints)
    
makeNotGeneralEnoughTypeError :: Bool -> Range -> UHA_Source -> TpScheme -> TpScheme -> TypeError
makeNotGeneralEnoughTypeError isAnnotation range source tpscheme1 tpscheme2 =
   let sub      = listToSubstitution (zip (ftv [tpscheme1, tpscheme2]) [ TVar i | i <- [1..] ])
       ts1      = skolemizeFTV (sub |-> tpscheme1)
       ts2      = skolemizeFTV (sub |-> tpscheme2)
       special  = if isAnnotation then "Type annotation" else "Type signature"
       oneliner = MessageOneLiner (MessageString (special ++ " is too general"))
       descr    = if isAnnotation then "expression" else "function"
       table    = [ descr           <:> MessageOneLineTree (oneLinerSource source)
                  , "declared type" >:> MessageType ts2
                  , "inferred type" >:> MessageType ts1
                  ]
       hints    = [ ("hint", MessageString "try removing the type signature") | not (null (ftv tpscheme1)) ] 
   in TypeError [range] [oneliner] table hints
   
makeMissingConstraintTypeError :: (Name -> Name) -> Range -> Maybe UHA_Source -> TpScheme -> (Bool, Predicate) -> UHA_Source -> TypeError
makeMissingConstraintTypeError unqualifier range mSource scheme (original, predicate) arisingFrom =
   let special  = if isJust mSource then "signature" else "annotation"
       oneliner = MessageOneLiner (MessageString ("Missing class constraint in type "++special))
       table    = maybe [] (\source -> ["function" <:> MessageOneLineTree (oneLinerSource source)]) mSource ++
                  [ (isJust mSource, MessageString "declared type", MessageType (convertTpScheme unqualifier scheme))
                  , "class constraint" <:> MessagePredicate (convertPredicate unqualifier predicate)
                  , "arising from"     >:> MessageOneLineTree (oneLinerSource arisingFrom)
                  ]
       hints    = [ ("hint", MessageString "add the class constraint to the type signature") | original ]
   in TypeError [range] [oneliner] table hints
   
makeUnresolvedOverloadingError :: UHA_Source -> String -> (TpScheme, TpScheme) -> TypeError
makeUnresolvedOverloadingError source description (functionType, usedAsType) =
   let message = [ MessageOneLiner (MessageString ("Don't know which instance to choose for " ++ description)) ]
       table   = [ "function" <:> MessageOneLineTree (oneLinerSource source)
                 , "type"     >:> MessageType functionType
                 , "used as"  >:> MessageType usedAsType
                 , "hint"     <:> MessageString ( "write an explicit type for this function" ++ 
                                "\n   e.g. (show :: [Int] -> String)")
                 ]
   in TypeError [rangeOfSource source] message table []
      
makeReductionError :: UHA_Source -> Either (TpScheme, Tp) (String, Maybe Tp) -> ClassEnvironment -> (Name -> Name) -> Predicate -> TypeError
makeReductionError source extra classEnvironment unqualifier (Predicate className predicateTp) =
   let location = either (const "function") fst extra
       message  = [ MessageOneLiner $ MessageString $ "Type error in overloaded " ++ location ]
       tab1     = case extra of 
                     Left (scheme, tp) -> -- overloaded function
                        [ "function" <:> MessageOneLineTree (oneLinerSource source)
                        , "type"     >:> MessageType (convertTpScheme unqualifier scheme)
                        , "used as"  >:> MessageType (toTpScheme tp)
                        ]
                     Right (_, mtp) -> -- overloaded language construct
                        (descriptionOfSource source <:> MessageOneLineTree (oneLinerSource source)) :
                        maybe [] (\tp -> ["type" >:> MessageType (toTpScheme tp)]) mtp
       tab2     = [ "problem"  <:> MessageCompose [ MessageType (toTpScheme predicateTp)
                                                  , MessageString (" is not an instance of class "++ unqualifierString className)
                                                  ]
                  ]
   in TypeError [rangeOfSource source] message (tab1 ++ tab2) [("hint", MessageString hint)]
   
  where  
    unqualifierTp     = convertTp unqualifier
    unqualifierString = convertString unqualifier
    hint = case valids of
              []  -> "there are no valid instances of "++unqualifierString className
              [x] -> "valid instance of "++unqualifierString className++" is "++show x
              _   -> "valid instances of "++unqualifierString className++" are "++prettyAndList (nub valids)
         
    valids :: [String]
    valids = let tps              = [ unqualifierTp tp | (Predicate _ tp, _) <- instances className classEnvironment ]
                 (tuples, others) = let p (TCon s) = isTupleConstructor s
                                        p _        = False
                                    in partition (p . fst . leftSpine) tps
                 f tp = listToSubstitution (zip (ftv tp) [ TCon s | s <- variableList ]) |-> tp
             in if length tuples > 4 -- magic number!
                  then map (show . f) others ++ ["tuples"]
                  else map (show . f) tps
                  
makeRestrictedButOverloadedError :: Name -> TpScheme -> TypeError
makeRestrictedButOverloadedError name scheme = 
   let message = MessageOneLiner $ MessageString $ "Illegal overloaded type inferred for " ++ show name
       table   = [ "variable"      <:> MessageString (show name)
                 , "inferred type" >:> MessageType scheme
                 ]
       hint    = "Only functions and simple patterns can have an overloaded type"
   in TypeError [getNameRange name] [message] table [("hint", MessageString hint)]
   
makeMissingInstancePredicateError :: Range -> Name -> String -> Predicate -> [(String, Name)] -> [(Name, Tp)] -> TypeError
makeMissingInstancePredicateError source className instanceName (Predicate predName tp) definedPredicates mapping =
    let 
        predicate = predName ++ " " ++ show (maybe (error "Invalid mapping") fst $ find (\x -> snd x == tp) mapping)
        message = MessageOneLiner $ MessageString $ "Missing predicate " ++ show predicate ++ " for instance definition of " ++ show className ++ " " ++ instanceName
        table = [
            "Predicates" <:> MessageString (intercalate ", " $ map (\(name, var) -> name ++ " " ++ show var) definedPredicates)
            ]
        hint = "Add the missing predicate to the instance definition"
    in TypeError [source] [message] table [("hint", MessageString hint)]