-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeErrors.hs : ...
-- 
-------------------------------------------------------------------------------

module TypeErrors where

import Messages
import Types
import List       (union)
import OneLiner   (OneLineTree)
import UHA_Syntax (Range)

type TypeErrors = [TypeError]
data TypeError  = TypeError
                     Range                    -- range of the error
                     MessageBlock             -- oneliner-message
                     TypeErrorTable           -- Hugs-like table
                     TypeErrorInfos           -- extra info (e.g. hints)

                | CustomTypeError
                     [Range]
                     Message

data TypeErrorTable = UnificationErrorTable
                         [(String, MessageBlock)]     -- sources to be reported
                         (Either Tp TpScheme) -- type or typescheme of n.t. or subterm of n.t.
                         (Either Tp TpScheme) -- conflicting type or expected type
                         
                    | NotGeneralEnoughTable           
                         OneLineTree          -- expression
                         TpScheme             -- declared type
                         TpScheme             -- inferred type

type TypeErrorInfos = [TypeErrorInfo]
data TypeErrorInfo  = TypeErrorHint String MessageBlock
                    | IsFolkloreTypeError
                    | HasDocumentationLink String

instance HasMessage TypeError where

   getMessage (TypeError range oneliner table infos) =
      let MessageTable newtable = makeMessageTable isFolklore table
          isFolklore = length [ () | IsFolkloreTypeError <- infos ] > 0
          hints      = [ (MessageString s, b) | TypeErrorHint s b <- infos ]
          emptyLine  = MessageOneLiner (MessageString "")
      in [MessageOneLiner oneliner, MessageTable (newtable ++ hints), emptyLine]

   getMessage (CustomTypeError ranges message) = message ++ [MessageOneLiner (MessageString "")]

   getRanges (TypeError range oneliner table infos) = [range]
   getRanges (CustomTypeError ranges message) = ranges

   getDocumentationLink = documentationLinkForTypeError

instance Substitutable TypeError where

   sub |-> (TypeError range oneliner table hints) =
      TypeError range (sub |-> oneliner) (sub |-> table) (sub |-> hints)

   sub |-> (CustomTypeError ranges message) =
      CustomTypeError ranges (sub |-> message)

   ftv (TypeError range oneliner table hints) =
      ftv oneliner `union` ftv table `union` ftv hints

   ftv (CustomTypeError ranges message) =
      ftv message

instance Substitutable TypeErrorTable where
   sub |-> (UnificationErrorTable sources type1 type2) =
      let type1'   = either (Left . (sub |->)) (Right . f) type1
          type2'   = either (Left . (sub |->)) (Right . f) type2
          sources' = [ (s, sub |-> mb) | (s, mb) <- sources ]
          f ts     = listToSubstitution [ (i, sub |-> TVar i) | i <- ftv ts ] |-> ts
      in (UnificationErrorTable sources' type1' type2') -- niet fraai
   sub |-> (NotGeneralEnoughTable tree tpscheme1 tpscheme2) =
      let sub' = listToSubstitution [ (i, sub |-> TVar i) | i <- ftv [tpscheme1, tpscheme2] ] -- niet fraai
      in (NotGeneralEnoughTable tree (sub' |-> tpscheme1) (sub' |-> tpscheme2))

   ftv (UnificationErrorTable sources type1 type2) = ftv (map snd sources) `union` ftv type1 `union` ftv type2
   ftv (NotGeneralEnoughTable tree tpscheme1 tpscheme2) = ftv tpscheme1 `union` ftv tpscheme2

instance Substitutable TypeErrorInfo where
   sub |-> (TypeErrorHint s mb) = TypeErrorHint s (sub |-> mb)
   sub |-> x                    = x

   ftv     (TypeErrorHint s mb) = ftv mb
   ftv _                        = []

makeMessageTable :: Bool -> TypeErrorTable -> MessageLine
makeMessageTable isFolklore typeErrorTable =
   case typeErrorTable of

      UnificationErrorTable sources type1 type2 ->
         let sourcePart = [ (MessageString s, t) | (s, t) <- sources ]
             typePart   = [ (MessageString "type", makeType type1)
                          , (MessageString reason, makeType type2)
                          ]
             reason     = if isFolklore
                            then "expected type"
                            else "does not match"
             makeType   = either MessageType MessageTypeScheme
         in MessageTable (sourcePart ++ typePart)

      NotGeneralEnoughTable tree tpscheme1 tpscheme2 ->
         MessageTable [ (MessageString "expression"   , MessageOneLineTree tree)
                      , (MessageString "declared type", MessageTypeScheme tpscheme1)
                      , (MessageString "inferred type", MessageTypeScheme tpscheme2)
                      ]


-- not a nice solution!
checkTypeError :: OrderedTypeSynonyms -> TypeError -> Maybe TypeError
checkTypeError synonyms typeError@(TypeError r o table h) =
   case table of
      UnificationErrorTable sources type1 type2 ->
         let becauseHint = TypeErrorHint "because" . MessageString
             fun i     = (\(_,_,a) -> a) . instantiate i
             unique    = maximum (0 : ftv type1 ++ ftv type2) + 1
             t1        = either id (fun unique) type1
             unique'   = maximum (0 : ftv t1 ++ ftv type2) + 1
             t2        = either id (fun unique') type2
         in
            case mguWithTypeSynonyms synonyms t1 t2 of
               Left InfiniteType  -> let hint = TypeErrorHint "because" (MessageString "unification would give infinite type")
                                     in Just (TypeError r o table (hint:h))
               Left ConstantClash -> Just typeError
               Right _            -> Nothing
               _        -> Just typeError
      _  -> Just typeError
checkTypeError synonyms typeError = Just typeError

makeNotGeneralEnoughTypeError :: Range -> OneLineTree -> TpScheme -> TpScheme -> TypeError
makeNotGeneralEnoughTypeError range tree tpscheme1 tpscheme2 =
   let sub      = listToSubstitution (zip (ftv [tpscheme1, tpscheme2]) [ TVar i | i <- [1..] ])
       ts1      = freezeFreeTypeVariables (sub |-> tpscheme1)
       ts2      = freezeFreeTypeVariables (sub |-> tpscheme2)
       oneliner = MessageString "Declared type is too general"
       table    = NotGeneralEnoughTable tree ts2 ts1
       hints    = if null (ftv tpscheme1)
                    then []
                    else [TypeErrorHint "hint" (MessageString "try removing the type signature")]
   in TypeError range oneliner table hints

documentationLinkForTypeError :: TypeError -> Maybe String
documentationLinkForTypeError typeError =
   case typeError of
      TypeError _ _ _ infos ->
         case [ s | HasDocumentationLink s <- infos ] of
            x:_ -> Just x
            _   -> Nothing
      _                     -> Nothing

