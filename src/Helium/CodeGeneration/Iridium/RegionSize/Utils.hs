module Helium.CodeGeneration.Iridium.RegionSize.Utils
    ( indent,
    varNames, typeVarName, annVarName,
    rsError, rsInfo
    ) where

import qualified Debug.Trace as T
import Data.List

-- | Indent a newline separated string
indent :: String -> String
indent = intercalate "\n" . map ((++) "  ") . splitOn '\n'

-- | Split string on character
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
varNames = map pure ['a'..'z'] ++ map ((++) "a" . (show :: Int -> String)) [1..]

-- | Get a type var name
typeVarName :: Int -> String
typeVarName idx | idx < 0 = "t_[" ++ show idx ++ "]"
                | otherwise = varNames !! idx

-- | Get a type var name
annVarName :: Int -> String
annVarName idx | idx < 0 = "v$[" ++ show idx ++ "]"
               | otherwise = varNames !! idx

----------------------------------------------------------------
-- Console messages
----------------------------------------------------------------

rsError :: String -> a
rsError s = error $ "[RegionSize] " ++ s ++ "\n"

rsInfo :: a -> String -> a
rsInfo v s = T.trace ("\n[RS_INFO] "++ s) v