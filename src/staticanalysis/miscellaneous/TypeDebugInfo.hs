module TypeDebugInfo 
   ( readTypeDebugInfo, writeTypeDebugInfo, TypeDebugInfo(..), Entry(..)
   , makeEntryId, EntryId, Pos, DefinitionInfo, TypeErrorInfo
   ) where

import Data.FiniteMap
import Top.Types

------------------------------------------------------

readTypeDebugInfo :: String -> IO TypeDebugInfo
readTypeDebugInfo file =
   do input <- readFile file
      return . toTypeDebugInfo . read $ input

writeTypeDebugInfo :: String -> TypeDebugInfo -> IO () 
writeTypeDebugInfo file ti =
   let InfoX s defs errs xs = fromTypeDebugInfo ti
   in writeFile file $
         "InfoX " ++ s ++ "\n" ++
         myShowList show defs ++
         myShowList show errs ++
         myShowList show xs

------------------------------------------------------

data TypeDebugInfo = TypeDebugInfo 
   { tiFileName    :: String
   , tiDefinitions :: [DefinitionInfo]
   , tiTypeErrors  :: [TypeErrorInfo]
   , tiEntries     :: FiniteMap EntryId Entry
   }

data TypeDebugInfoX = InfoX String [DefinitionInfo] [TypeErrorInfo] [EntryX]
   deriving Read

toTypeDebugInfo :: TypeDebugInfoX -> TypeDebugInfo
toTypeDebugInfo (InfoX file defs errs xs) = 
   TypeDebugInfo { tiFileName    = file
                 , tiDefinitions = defs
                 , tiTypeErrors  = errs
                 , tiEntries     = listToFM (map toEntry xs)
                 }

fromTypeDebugInfo :: TypeDebugInfo -> TypeDebugInfoX
fromTypeDebugInfo ti = 
   InfoX (tiFileName ti) 
         (tiDefinitions ti) 
         (tiTypeErrors ti)
         (map fromEntry $ fmToList $ tiEntries ti) 
   
------------------------------------------------------

data Entry = Entry 
   { getRange       :: (Pos, Pos)
   , getDescription :: String
   , getNonTerminal :: String
   , getPretty      :: String
   , getMType       :: Maybe Tp
   , getMOriginal   :: Maybe TpScheme
   , getMono        :: [Int]
   , getParent      :: Maybe EntryId
   , getSubTerms    :: [EntryId]
   }

data EntryX = X Int (Pos, Pos) String String String (Maybe String) (Maybe String) [Int] (Maybe Int) [Int]
   deriving (Show, Read)

toEntry :: EntryX -> (EntryId, Entry)
toEntry (X i ran descr nt pp tp or mono par subs) = 
   let entry = Entry { getRange       = ran
                     , getDescription = descr
                     , getNonTerminal = nt
                     , getPretty      = pp 
                     , getMType       = fmap read tp
                     , getMOriginal   = fmap readTpScheme or
                     , getMono        = mono
                     , getParent      = fmap EntryId par
                     , getSubTerms    = map EntryId subs
                     }
   in (EntryId i, entry) 
               
fromEntry :: (EntryId, Entry) -> EntryX
fromEntry (EntryId i, entry) =
   X i (getRange entry) 
       (getDescription entry) 
       (getNonTerminal entry) 
       (getPretty entry) 
       (fmap show $ getMType entry) 
       (fmap showTpScheme $ getMOriginal entry) 
       (getMono entry) 
       (fmap (\(EntryId i) -> i) $ getParent entry) 
       [i | EntryId i <- getSubTerms entry ]

------------------------------------------------------

type Pos     = (Int, Int)
data EntryId = EntryId Int 
   deriving (Eq, Ord)

type DefinitionInfo = ([String], (Pos, Pos))
type TypeErrorInfo  = ([(Pos, Pos)], String)

makeEntryId :: Int -> EntryId
makeEntryId = EntryId
   
showTpScheme :: TpScheme -> String
showTpScheme scheme =
   let (ps, tp) = split (unquantify scheme)
   in "(" ++ show (quantifiers scheme) ++ "," ++ show ps ++ "," ++ show tp ++ ")"
      
readTpScheme :: String -> TpScheme
readTpScheme s =
   let (qs, ps, tp) = read s :: ([Int], [Int], Tp)
   in quantify qs ([] .=>. tp)

myShowList :: (a -> String) -> [a] -> String
myShowList f [] = "[]"
myShowList f xs = 
   unlines (zipWith (++) ("[ ": repeat ", ") (map f xs) ++ ["]"])