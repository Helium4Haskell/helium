module Helium.CodeGeneration.Iridium.RegionSize.Utils
    ( indent,
    varNames,
    rsError, rsInfo
    ) where

import qualified Debug.Trace as T
import Data.List

-- | Indent a newline separated string
indent :: String -> String
indent = intercalate "\n" . map ((++) "  ") . splitOn '\n'

splitOn :: Char -> String -> [String]
splitOn c s = case dropWhile ((==) c) s of
                     "" -> []
                     s' -> let (w, s'') = break ((==) c) s'
                           in w : splitOn c s''

----------------------------------------------------------------
-- Helper data
----------------------------------------------------------------

-- | Infinite list of variable names
varNames :: [String]
varNames = (:) "#ERROR 0 INDEX#" $ map pure ['a'..'z'] ++ map ((++) "a" . (show :: Int -> String)) [1..]

----------------------------------------------------------------
-- Console messages
----------------------------------------------------------------

rsError :: String -> a
rsError = error . (++) "[RegionSize] " 

rsInfo :: a -> String -> a
rsInfo v s = T.trace ("\n[INFO] "++ s) v