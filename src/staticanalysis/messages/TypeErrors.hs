{-| Module      :  TypeErrors
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Errors that are constructed during type inferece.
-}

module TypeErrors where

import Messages
import Top.Types
import List       (union, intersperse, partition)
import OneLiner   (OneLineTree(..) )
import UHA_Syntax (Range, Name)
import UHA_Source

type TypeErrors = [TypeError]
data TypeError  = TypeError
                     [Range]                    -- range(s) of the error
                     [MessageLine]              -- oneliner messages
                     [(String, MessageBlock)]   -- Hugs-like table
                     [TypeErrorHint]            -- extra hints
		     
type TypeErrorHint  = (String, MessageBlock)

instance HasMessage TypeError where
   getMessage (TypeError range oneliners table hints) =
      let emptyLine  = MessageOneLiner (MessageString "")
	  maybeTable | null table = [] 
	             | otherwise  = [MessageTable [ (MessageString s, t) | (s, t) <- (table ++ hints) ]]
      in oneliners ++ maybeTable ++ [emptyLine]
   getRanges (TypeError ranges oneliner table hints) = ranges

instance Substitutable TypeError where
   sub |-> (TypeError ranges oneliner table hints) =
      let f xs = [ (s, sub |-> b) | (s, b) <- xs ] 
      in TypeError ranges (sub |-> oneliner) (f table) (f hints)
   ftv (TypeError ranges oneliner table hints) =
      ftv oneliner `union` ftv (map snd table) `union` ftv (map snd hints)
	
makeNotGeneralEnoughTypeError :: UHA_Source -> TpScheme -> TpScheme -> TypeError
makeNotGeneralEnoughTypeError source tpscheme1 tpscheme2 =
   let sub      = listToSubstitution (zip (ftv [tpscheme1, tpscheme2]) [ TVar i | i <- [1..] ])
       ts1      = skolemizeFTV (sub |-> tpscheme1)
       ts2      = skolemizeFTV (sub |-> tpscheme2)
       oneliner = MessageOneLiner (MessageString "Declared type is too general")
       table    = [ ("function"     , MessageOneLineTree (oneLinerSource source))
                  , ("declared type", MessageType ts2)
		  , ("inferred type", MessageType ts1)
                  ]
       hints    = [ ("hint", MessageString "try removing the type signature") | not (null (ftv tpscheme1)) ] 
   in TypeError [rangeOfSource source] [oneliner] table hints
   
makeMissingConstraintTypeError :: Either Name UHA_Source -> TpScheme -> TpScheme -> TypeError
makeMissingConstraintTypeError mySource tpscheme1 tpscheme2 =
   let source   = either nameToUHA_Expr id mySource
       sub      = listToSubstitution (zip (ftv [tpscheme1, tpscheme2]) [ TVar i | i <- [1..] ])
       ts1      = skolemizeFTV (sub |-> tpscheme1)
       ts2      = skolemizeFTV (sub |-> tpscheme2)
       oneliner = MessageOneLiner (MessageString "Missing class constraint in declared type")
       table    = [ ("function"     , MessageOneLineTree (oneLinerSource source))
                  , ("declared type", MessageType ts2)
		  , ("inferred type", MessageType ts1)
                  ]
       hint     = ("hint", MessageString ("add a class constraint to the type signature" ++
                                          special ++ " (see inferred type)"))
       special  = either (\n -> " for " ++ show n) (const "") mySource
   in TypeError [rangeOfSource source] [oneliner] table [hint]
   
makeUnresolvedOverloadingError :: UHA_Source -> String -> (TpScheme, TpScheme) -> TypeError
makeUnresolvedOverloadingError source description (functionType, usedAsType) =
   let message = [ MessageOneLiner (MessageString ("Don't know which instance to choose for " ++ description)) ]
       table   = [ ("function" , MessageOneLineTree (oneLinerSource source)) 
                 , ("type"     , MessageType functionType)
		 , ("used as"  , MessageType usedAsType)
                 , ("hint"     , MessageString ( "write an explicit type for this function" ++ 
		                                 "\n   e.g. (show :: [Int] -> String)")) 
                 ]
   in TypeError [rangeOfSource source] message table []
      
makeReductionError :: UHA_Source -> (TpScheme, Tp) -> ClassEnvironment -> Predicate -> TypeError
makeReductionError source (scheme, tp) classEnvironment predicate@(Predicate className predicateTp) =
   let message = [ MessageOneLiner (MessageString "Type error in overloaded function") ]
       table   = [ ("function", MessageOneLineTree (oneLinerSource source)) 
                 , ("type"    , MessageType scheme)
                 , ("used as" , MessageType (toTpScheme tp))
                 , ("problem" , MessageCompose [ MessageType (toTpScheme predicateTp)
                                               , MessageString (" is not an instance of class "++className)
				               ])
                 ]
   in TypeError [rangeOfSource source] message table [("hint", MessageString hint)]
   
  where  
    hint :: String
    hint = case valids of
              []  -> "there are no valid instances of "++className
              [x] -> "valid instance of "++className++" is "++show x
              xs  -> "valid instances of "++className++" are "++prettyAndList valids
         
    valids :: [String]
    valids = let tps              = [ tp | (Predicate _ tp, _) <- instances className classEnvironment ]
                 (tuples, others) = let p (TCon s) = isTupleConstructor s
                                        p _        = False
                                    in partition (p . fst . leftSpine) tps
                 f tp = listToSubstitution (zip (ftv tp) [ TCon s | s <- variableList ]) |-> tp
             in if length tuples > 4 -- magic number!
                  then map (show . f) others ++ ["tuples"]
                  else map (show . f) tps