-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- HeliumMessages.hs : ...
-- 
-------------------------------------------------------------------------------

module HeliumMessages where

import Messages 
import Types
import qualified PPrint
import qualified OneLiner
import List                (intersperse, zipWith4)
import TypesToAlignedDocs  (typesToAlignedDocs)
import UHA_Utils           (isImportRange)
import Char                (isSpace)

sortAndShowMessages :: (Show a, HasMessage a) => [a] -> String
sortAndShowMessages = concatMap show . sortMessages

lineLength :: Int
lineLength = 80
                  
instance Show MessageLine where
   show messageLine = 
      case prepareTypesAndTypeSchemes messageLine of
         MessageOneLiner m   -> show m++"\n"
         MessageTable tab    -> showTable tab
         MessageHints pre ms -> showHints pre ms

instance Show MessageBlock where
   show (MessageString s     ) = s
   show (MessageRange r      ) = show r
   show (MessageType tp      ) = show tp
   show (MessageTypeScheme ts) = show ts
   show (MessageOneLineTree t) =  -- see tableWidthRight
                                 OneLiner.showOneLine 59 t
   show (MessageCompose ms   ) = concatMap show ms

instance HasMessage message => Show message where
   show x = let rangePart = MessageString $ case filter (not . isImportRange) (getRanges x) of
                               [] -> ""
                               xs -> showPositions xs ++ ": "
                list = case getMessage x of
                           []                     -> [MessageOneLiner rangePart]
                           MessageOneLiner m:rest -> MessageOneLiner (MessageCompose [rangePart,m]) : rest
                           xs                     -> MessageOneLiner rangePart : xs
            in concatMap show list

showHints :: String -> MessageBlocks -> String
showHints pre ms = 
   let firstPrefix = "  " ++ pre ++ " - "
       restPrefix  = replicate (2 + length pre) ' ' ++ " - "
       emptyPrefix = replicate (5 + length pre) ' '
       width       = lineLength - length firstPrefix
       combine     = concat . intersperse ("\n" ++ emptyPrefix)
       prefixes    = firstPrefix : repeat restPrefix
   in unlines . zipWith (++) prefixes . map (combine . splitString width . show) $ ms

tableWidthLeft :: Int
tableWidthLeft = 14

tableWidthRight :: Int
tableWidthRight = lineLength - tableWidthLeft - 7 -- see leftStars and middleSep

showTable :: [(MessageBlock, MessageBlock)] -> String
showTable = let leftStars = "*** "
                middleSep = " : "
                showTuple (x, y) = 
                   let zipf a b c d = a ++ b ++ c ++ d 
                       xs  = splitString tableWidthLeft  (show x)                   
                       ys  = splitString tableWidthRight (show y)
                       i   = length xs `max` length ys
                       xs' = map (\s -> take tableWidthLeft (s++repeat ' ')) (xs ++ repeat "")
                       ys' = ys ++ repeat (replicate tableWidthRight ' ')
                       left   = leftStars : repeat "    "
                       middle = middleSep : repeat "   "
                   in unlines (take i (zipWith4 zipf left xs' middle ys'))
            in concatMap showTuple . renderTypesInRight tableWidthRight

-- if two types or type schemes follow each other in a table (on the right-hand side)
-- then the two types are rendered in a special way.
renderTypesInRight :: Int -> [(MessageBlock, MessageBlock)] -> [(MessageBlock, MessageBlock)]
renderTypesInRight width table = 
   case table of
      (l1, r1) : (l2, r2) : rest 
        -> case (maybeType r1, maybeType r2) of
              (Just tp1, Just tp2) -> let [doc1, doc2] = typesToAlignedDocs [tp1, tp2]
                                          render = flip PPrint.displayS [] . PPrint.renderPretty 1.0 width
                                      in (l1, MessageString (render doc1)) 
                                       : (l2, MessageString (render doc2)) 
                                       : renderTypesInRight width rest
              _                    -> (l1, r1) : renderTypesInRight width ((l2, r2) : rest)
      _ -> table 

  where maybeType :: MessageBlock -> Maybe Tp
        maybeType (MessageType tp      ) = Just tp
        maybeType (MessageTypeScheme ts) = Just (unsafeInstantiate ts)
        maybeType _                      = Nothing

-- make sure that a string does not exceed a certain with.
-- Two extra features:
--   - treat '\n' in the proper way.
--     (Be careful here: an enter in a string or a character does not 
--      make a new line)
--   - try not to break words.
splitString :: Int -> String -> [String]
splitString width = concatMap f . lines 
   where f string | length string <= width
                    = [string]
                  | otherwise 
                    = let lastSpace     = last . (width:) . map fst . filter predicate 
                                               . zip [0..] . take width $ string
                          predicate (pos, char) = isSpace char && pos >= width - splitStringMargin
                          (begin, rest) = splitAt lastSpace string
                      in begin : f (dropWhile isSpace rest)                   
                    
splitStringMargin :: Int
splitStringMargin = 15

-- Prepare the types and type schemes in a messageline to be shown.
-- 
-- type schemes:
--   * responsible for their own type variables
--   * monomorphic type variables are frozen, that is, replaced by _1, _2, etc.
-- types: 
--   * use a, b, c for type variables
--   * use the type variables consistent over all types 
--       (for instance, all v5 are mapped to a 'c')
prepareTypesAndTypeSchemes :: MessageLine -> MessageLine
prepareTypesAndTypeSchemes messageLine = newMessageLine
   where 
    (result, _, names) = replaceTypeSchemes messageLine
    newMessageLine     = giveTypeVariableIdentifiers result
   
     --step 1
    replaceTypeSchemes :: MessageLine -> (MessageLine, Int, [String])
    replaceTypeSchemes messageLine = 
       let unique = maximum (0 : ftv messageLine) + 1
       in case messageLine of
             MessageOneLiner mb -> let (r, i, ns) = f_MessageBlock unique mb
                                   in (MessageOneLiner r, i, ns)
             MessageTable tab   -> let (r, i, ns) = f_Table unique tab
                                   in (MessageTable r, i, ns)
             MessageHints s mbs -> let (r, i, ns) = f_MessageBlocks unique mbs
                                   in (MessageHints s r, i, ns)
    
    --step 2
    giveTypeVariableIdentifiers :: MessageLine -> MessageLine        
    giveTypeVariableIdentifiers ml = 
       let sub = listToSubstitution (zip (ftv ml) [ TCon [c] | c <- ['a'..], [c] `notElem` names])
       in sub |-> ml
   
    f_Table :: Int -> [(MessageBlock, MessageBlock)] -> ([(MessageBlock, MessageBlock)], Int, [String])
    f_Table i [] = ([], i, [])
    f_Table i ((a, b):xs) = let (r1, i1, ns1) = f_MessageBlock i  a
                                (r2, i2, ns2) = f_MessageBlock i1 b
                                (r3, i3, ns3) = f_Table        i2 xs
                            in ((r1, r2):r3, i3, ns1++ns2++ns3)    
    
    f_MessageBlocks :: Int -> [MessageBlock] -> ([MessageBlock], Int, [String])
    f_MessageBlocks i []     = ([], i, [])
    f_MessageBlocks i (x:xs) = let (r1, i1, ns1) = f_MessageBlock  i  x
                                   (r2, i2, ns2) = f_MessageBlocks i1 xs
                               in (r1:r2, i2, ns1++ns2)
    
    f_MessageBlock :: Int -> MessageBlock -> (MessageBlock, Int, [String])
    f_MessageBlock unique messageBlock = 
        case messageBlock of
           MessageCompose mbs   -> let (r, i, ns) = f_MessageBlocks unique mbs
                                   in (MessageCompose r, i, ns)
           MessageTypeScheme ts -> let (unique', its) = instantiateWithNameMap unique ts
                                   in (MessageType its, unique', constantsInType its)
           _                    -> (messageBlock, unique, [])
