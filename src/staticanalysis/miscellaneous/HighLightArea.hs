-----------------------------------------------------------------------------
-- |The Helium Compiler : Static Analysis
-- 
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- An area is a list of ranges which can be used, for instance, to highlight
-- parts of a program.
--
-----------------------------------------------------------------------------

module HighLightArea where

import UHA_Syntax
import UHA_Range (showFullRange)
import Data.List

----------------------------------------------------------------------------------------
-- Areas to highlight
	
newtype Area = Area [Range]

instance Show Area where
   show (Area ranges) = 
      concat (intersperse "," (map showFullRange ranges))

-------------------------------------------------------------------------------------------
-- Functions to construct and combine areas
	
empty :: Area
empty = Area []

plus :: [Area] -> Area
plus = foldr (.+.) empty

-- |Convert a range into an area.
rangeToArea :: Range -> Area
rangeToArea range = Area [range]

-- |The union of two areas.
(.+.) :: Area -> Area -> Area
Area xs .+. Area ys = 
   let insert range@(Range_Range startPos endPos) ranges =
          case ranges of
	     [] -> [range]
	     this@(Range_Range p1 p2) : rest 
	        | p2 <  startPos -> this : insert range rest
		| p2 == startPos -> insert (Range_Range p1 endPos) rest
		| endPos <  p1   -> range : this : rest
		| endPos == p1   -> Range_Range startPos p2 : rest
		| otherwise      -> insert (Range_Range (startPos `min` p1) (endPos `max` p2)) rest
   in Area (foldr insert xs ys)

-- |Given two areas, subtract the latter from the former.
(.-.) :: Area -> Area -> Area
Area xs .-. Area ys = 
   let removeList []     x = [x]
       removeList (y:ys) x = concatMap (removeList ys) (removeOne y x)
       removeOne (Range_Range y1 y2) x@(Range_Range x1 x2)
          | y2 <= x1 = [x] -- the ranges do not overlap
	  | x2 <= y1 = [x] -- the ranges do not overlap
	  | otherwise = 
	       let stop1 = x2 `min` y1
	           stop2 = x1 `max` y2 
	       in [ Range_Range x1 stop1 | x1 < stop1 ]
	       ++ [ Range_Range stop2 x2 | x1 < stop2, stop2 < x2 ]
   in Area (concatMap (removeList ys) xs)
