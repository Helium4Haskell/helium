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
import TypesToAlignedDocs  (showTwoTypesSpecial)
import UHA_Utils           (isImportRange)
import Char                (isSpace)

sortAndShowMessages :: (Show a, HasMessage a) => [a] -> String
sortAndShowMessages = concatMap show . sortMessages

lineLength :: Int
lineLength = 80
                  
instance Show MessageLine where
   show (MessageOneLiner m   ) = show m++"\n"
   show (MessageTable tab    ) = showTable tab
   show (MessageHints pre ms ) = showHints pre ms

instance Show MessageBlock where
   show (MessageString s     ) = s
   show (MessageRange r      ) = show r
   show (MessageType tp      ) = show tp
   show (MessageTypeScheme ts) = show (instantiateWithNameMap (head (freezeMonosInTypeSchemes [ts])))
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
              (Just tp1, Just tp2) -> let (doc1,doc2) = showTwoTypesSpecial (tp1, tp2)
                                          render = flip PPrint.displayS [] . PPrint.renderPretty 1.0 width
                                      in (l1, MessageString (render doc1)) 
                                       : (l2, MessageString (render doc2)) 
                                       : renderTypesInRight width rest
              _                    -> (l1, r1) : renderTypesInRight width ((l2, r2) : rest)
      _ -> table 

  where maybeType :: MessageBlock -> Maybe Tp
        maybeType (MessageType tp      ) = Just tp
        maybeType (MessageTypeScheme ts) = Just (instantiateWithNameMap ts)
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
