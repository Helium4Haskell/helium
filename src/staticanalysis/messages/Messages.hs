-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Messages.hs : ...
-- 
-------------------------------------------------------------------------------

module Messages where

import UHA_Syntax
import UHA_Utils
import Types 
import qualified OneLiner
import Similarity (similar)
import Utils      (internalError)
import List       (sortBy, sort, partition)
import Maybe      (fromJust, isNothing)
import Char       (toUpper)

type Message       = [MessageLine] 

data MessageLine   = MessageOneLiner  MessageBlock
                   | MessageTable     [(MessageBlock, MessageBlock)]
                   | MessageHints     String MessageBlocks

type MessageBlocks = [MessageBlock]               
data MessageBlock  = MessageString       String
                   | MessageRange        Range
                   | MessageType         Tp
                   | MessageTypeScheme   TpScheme
                   | MessageInfoLink     String
                   | MessageOneLineTree  OneLiner.Tree
                   | MessageCompose      MessageBlocks                   
                  
class HasMessage a where
   getRanges            :: a -> [Range]
   getDocumentationLink :: a -> Maybe String
   getMessage           :: a -> Message  
   
   -- default definitions
   getRanges            _ = []
   getDocumentationLink _ = Nothing
   

instance Substitutable MessageLine where

   sub |-> ml = case ml of   
                   MessageOneLiner mb -> MessageOneLiner (sub |-> mb)
                   MessageTable table -> MessageTable (sub |-> table)
                   MessageHints s mbs -> MessageHints s (sub |-> mbs)

   ftv ml = case ml of
               MessageOneLiner mb -> ftv mb
               MessageTable table -> ftv table
               MessageHints s mbs -> ftv mbs
                                       
instance Substitutable MessageBlock where

   sub |-> mb = case mb of
                   MessageType tp       -> MessageType (sub |-> tp)
                   MessageTypeScheme ts -> -- see "substitution is static"
                                           let sub' = listToSubstitution [ (i, sub |-> TVar i) | i <- ftv ts ]
                                           in MessageTypeScheme (sub' |-> ts)
                   MessageCompose mbs   -> MessageCompose (sub |-> mbs) 
                   _                    -> mb

   ftv mb = case mb of         
               MessageType tp       -> ftv tp
               MessageTypeScheme ts -> ftv ts
               MessageCompose mbs   -> ftv mbs
               _                    -> []       

-------------------------------------------------------------
-- Misc

data Entity = TypeSignature
            | TypeVariable
            | TypeConstructor
            | Definition
            | Constructor
            | Variable
            | Import
            | ExportVariable
            | ExportModule
            | ExportConstructor
            | ExportTypeConstructor
            | Fixity
    deriving Eq

sortOnRangeEnd :: [Range] -> [Range]
sortOnRangeEnd =
    sortBy
        (\x y ->
            compare
                (getRangeEnd x)
                (getRangeEnd y)
        )

showPositions :: [Range] -> String
showPositions rs = showPositions' (sort rs)
showPositions' :: [Range] -> String
showPositions' (range:ranges) = showPosition range ++ concatMap ((", " ++) . showPosition) ranges
showPositions' [] = "<unknownNR>"

-- !!!! In the special case that the range corresponds to the import range,
-- the module name of the second position should be printed
showPosition :: Range -> String
showPosition range@(Range_Range _ (Position_Position modName _ _))
    | isImportRange range =
        modName
showPosition (Range_Range (Position_Position _ l c) _) =
    "(" ++ show l ++ "," ++ show c ++ ")"
showPosition (Range_Range Position_Unknown Position_Unknown) =
    "<unknownSP1>"
showPosition (Range_Range Position_Unknown _) =
    "<unknownSP2>"
showPosition _ =
    internalError "SAMessages" "showPosition" "unknown kind of position"

sortMessages :: HasMessage a => [a] -> [a]
sortMessages = let f x y = compare (sortRanges (getRanges x)) 
                                   (sortRanges (getRanges y))
               in sortBy f

sortRanges :: [Range] -> [Range]
sortRanges ranges = let (xs,ys) = partition isImportRange ranges
                    in sort ys ++ xs

sortNamesByRange :: Names -> Names
sortNamesByRange names = 
   let tupleList = [ (name, getNameRange name) | name <- names ]
       (xs,ys)   = partition (isImportRange . snd) tupleList
   in map fst (sortBy (\a b -> snd a `compare` snd b) ys ++ xs)

                                        
showFullRange :: Range -> String
showFullRange (Range_Range p1 p2) = "<" ++ showFullPosition p1 ++ "," ++ showFullPosition p2 ++ ">"

showFullPosition :: Position -> String
showFullPosition (Position_Position m l c) = "<" ++ m ++ "," ++ show l ++ "," ++ show c ++ ">"
showFullPosition (Position_Unknown) = "<unknownFP>"

prettyOrList :: [String] -> String
prettyOrList []  = ""
prettyOrList [s] = s
prettyOrList xs  = foldr1 (\x y -> x++", "++y) (init xs) ++ " or "++last xs

prettyAndList :: [String] -> String
prettyAndList []  = ""
prettyAndList [s] = s
prettyAndList xs  = foldr1 (\x y -> x++", "++y) (init xs) ++ " and "++last xs

prettyNumberOfParameters :: Int -> String
prettyNumberOfParameters 0 = "no parameters"
prettyNumberOfParameters 1 = "1 parameter"
prettyNumberOfParameters n = show n++" parameters"
                    
capitalize :: String -> String
capitalize (x:xs) = toUpper x : xs

findSimilar :: Name -> Names -> Names
findSimilar n = filter (\n' -> show n `similar` show n')

instance Show Entity where
   show entity = case entity of
                  TypeSignature   -> "type signature"
                  TypeVariable    -> "type variable"
                  TypeConstructor -> "type constructor"
                  Definition      -> "definition"
                  Constructor     -> "constructor"
                  Variable        -> "variable"
                  Import          -> "import"
                  ExportVariable  -> "exported variable"
                  ExportModule    -> "exported module"
                  ExportConstructor
                                  -> "exported constructor"
                  ExportTypeConstructor
                                  -> "exported type constructor"
                  Fixity          -> "infix declaration"
                  _               -> internalError "SAMessages" "instance Show Entity" "unknown entity"
