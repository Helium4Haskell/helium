-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
-- 
-------------------------------------------------------------------------------

module TypeErrors where

import Messages
import Top.Types
import List       (union, intersperse, partition)
import OneLiner   (OneLineTree(..) )
import UHA_Syntax (Range, Name)
import UHA_Source

type TypeErrors = [TypeError]
data TypeError  = TypeError
                     [Range]                  -- range(s) of the error
                     MessageLine              -- oneliner-message
                     TypeErrorTable           -- Hugs-like table
                     TypeErrorInfo            -- extra info (e.g. hints)

                | CustomTypeError
                     [Range]
                     Message

data TypeErrorTable = UnificationErrorTable
                         [(String, MessageBlock)]     -- sources to be reported
                         TpScheme                     -- type of n.t. or subterm of n.t.
                         TpScheme                     -- conflicting type or expected type
                         
                    | NotGeneralEnoughTable           
                         MessageBlock         -- expression
                         TpScheme             -- declared type
                         TpScheme             -- inferred type

type TypeErrorInfo = ([TypeErrorHint], Bool {- isFolklore -})
type TypeErrorHint = (String, MessageBlock)

instance HasMessage TypeError where

   getMessage (TypeError range oneliner table (hints, isFolklore)) =
      let MessageTable newtable = makeMessageTable isFolklore table
          hints'    = [ (MessageString s, b) | (s, b) <- hints ]
          emptyLine = MessageOneLiner (MessageString "")
      in [oneliner, MessageTable (newtable ++ hints'), emptyLine]

   getMessage (CustomTypeError ranges message) = message ++ [MessageOneLiner (MessageString "")]

   getRanges (TypeError ranges oneliner table infos) = ranges
   getRanges (CustomTypeError ranges message) = ranges

instance Substitutable TypeError where

   sub |-> (TypeError ranges oneliner table (hints, isFolklore)) =
      let hints' = [ (s, sub |-> b) | (s, b) <- hints ] 
      in TypeError ranges (sub |-> oneliner) (sub |-> table) (hints', isFolklore)

   sub |-> (CustomTypeError ranges message) =
      CustomTypeError ranges (sub |-> message)

   ftv (TypeError _ oneliner table (hints, _)) =
      ftv oneliner `union` ftv table `union` ftv (map snd hints)

   ftv (CustomTypeError _ message) =
      ftv message

instance Substitutable TypeErrorTable where
   sub |-> (UnificationErrorTable sources type1 type2) =
      let sources' = [ (s, sub |-> mb) | (s, mb) <- sources ]
      in UnificationErrorTable sources' (sub |-> type1) (sub |-> type2)
   sub |-> (NotGeneralEnoughTable tree tpscheme1 tpscheme2) =
      NotGeneralEnoughTable tree (sub |-> tpscheme1) (sub |-> tpscheme2)

   ftv (UnificationErrorTable sources type1 type2) = 
      ftv (map snd sources) `union` ftv type1 `union` ftv type2
   ftv (NotGeneralEnoughTable tree tpscheme1 tpscheme2) = 
      ftv tpscheme1 `union` ftv tpscheme2

makeMessageTable :: Bool -> TypeErrorTable -> MessageLine
makeMessageTable isFolklore typeErrorTable =
   case typeErrorTable of

      UnificationErrorTable sources type1 type2 ->
         let sourcePart = [ (MessageString s, t) | (s, t) <- sources ]
             typePart   = [ (MessageString "type", MessageType type1)
                          , (MessageString reason, MessageType type2)
                          ]
             reason     = if isFolklore
                            then "expected type"
                            else "does not match"
         in MessageTable (sourcePart ++ typePart)

      NotGeneralEnoughTable tree tpscheme1 tpscheme2 ->
         MessageTable [ (MessageString "expression"   , tree)
                      , (MessageString "declared type", MessageType tpscheme1)
                      , (MessageString "inferred type", MessageType tpscheme2)
                      ]

-- not a nice solution!
checkTypeError :: OrderedTypeSynonyms -> TypeError -> Maybe TypeError
checkTypeError synonyms typeError@(TypeError r o table (hints, isFolklore)) =
   case table of
      UnificationErrorTable sources type1 type2 ->
         let fun i   = unqualify . snd . instantiate i
             unique  = nextFTV [type1, type2]
             t1      = fun unique type1
             unique' = maximum (0 : ftv t1 ++ ftv type2) + 1
             t2      = fun unique' type2
         in case mguWithTypeSynonyms synonyms t1 t2 of
               Left (InfiniteType _) -> 
	          let hint = ("because", MessageString "unification would give infinite type")
                  in Just (TypeError r o table (hint:hints, isFolklore))
               Left _  -> Just typeError
               Right _ -> Nothing
      _  -> Just typeError
checkTypeError synonyms typeError = Just typeError

makeNotGeneralEnoughTypeError :: UHA_Source -> TpScheme -> TpScheme -> TypeError
makeNotGeneralEnoughTypeError source tpscheme1 tpscheme2 =
   let sub      = listToSubstitution (zip (ftv [tpscheme1, tpscheme2]) [ TVar i | i <- [1..] ])
       ts1      = skolemizeFTV (sub |-> tpscheme1)
       ts2      = skolemizeFTV (sub |-> tpscheme2)
       oneliner = MessageOneLiner (MessageString "Declared type is too general")
       table    = NotGeneralEnoughTable (MessageOneLineTree (oneLinerSource source)) ts2 ts1
       hints    = [ ("hint", MessageString "try removing the type signature") | not (null (ftv tpscheme1)) ] 
   in TypeError [rangeOfSource source] oneliner table (hints, False)
   
makeUnresolvedOverloadingError :: UHA_Source -> Predicate -> TypeError
makeUnresolvedOverloadingError source predicate =
   CustomTypeError [rangeOfSource source]
      [ MessageOneLiner (MessageString "Unresolved overloading")
      , MessageTable
           [ (MessageString "function" , MessageOneLineTree (oneLinerSource source)) 
           , (MessageString "predicate", MessagePredicate predicate)
           ]
      ]
      
makeReductionError :: UHA_Source -> (TpScheme, Tp) -> ClassEnvironment -> Predicate -> TypeError
makeReductionError source (scheme, tp) classEnvironment predicate@(Predicate className predicateTp) =
   CustomTypeError [rangeOfSource source] 
      [ MessageOneLiner (MessageString "Type error in overloaded function")
      , MessageTable 
           [ (MessageString "function", MessageOneLineTree (oneLinerSource source)) 
           , (MessageString "type"    , MessageType scheme)
           , (MessageString "used as" , MessageType (toTpScheme tp))
           , (MessageString "problem" , MessageCompose [ MessageType (toTpScheme predicateTp)
                                                       , MessageString (" is not an instance of class "++className)
						       ])
           ]
      , MessageOneLiner (MessageString hint)
      ]

   where hint :: String
         hint = case valids of
                   []  -> "  hint: there are no valid instances of "++className
                   [x] -> "  hint: valid instance of "++className++" is "++show x
                   xs  -> "  hint: valid instances of "++className++" are "++prettyAndList valids
         
         valids :: [String]
         valids = let tps              = [ tp | (Predicate _ tp, _) <- instances className classEnvironment ]
                      (tuples, others) = let p (TCon s) = isTupleConstructor s
                                             p _        = False
                                         in partition (p . fst . leftSpine) tps
                      f tp = listToSubstitution (zip (ftv tp) [ TCon s | s <- variableList ]) |-> tp
                  in if length tuples > 4 -- magic number!
                       then map (show . f) others ++ ["tuples"]
                       else map (show . f) tps