module Helium.CodeGeneration.Iridium.RegionSize.Utils
    (weakenIdx, strengthenIdx,
    indent, strIsReg,
    varNames, typeVarName, annVarName,
    rsError, rsInfo,
    mapAccumLM, mapWithIndex
    ) where

import qualified Debug.Trace as T
import Data.List

----------------------------------------------------------------
-- De bruijn reinexing
----------------------------------------------------------------

type Depth = Int
type Index = Int

-- | Increase unbound indexes by subD
weakenIdx :: Int -> Depth -> Index -> Index
weakenIdx subD d idx = if idx > d -- If idx >= d: var points outside of applicated term 
                        then idx + subD -- Reindex
                        else idx 

-- | Increase unbound indexes by 1
strengthenIdx :: Depth -> Index -> Index
strengthenIdx d idx = if idx > d
                      then idx - 1 
                      else idx

----------------------------------------------------------------
-- Indenting
----------------------------------------------------------------

-- | Check if a string is a region
strIsReg :: String -> Bool
strIsReg (c:_) = c == 'ρ'
strIsReg ""    = False

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
-- De bruijn index variable names
----------------------------------------------------------------

-- | Infinite list of variable names
varNames :: [String]
varNames = map pure ['a'..'z'] ++ map ((++) "a" . (show :: Int -> String)) [1..]

-- | Get a type var name
typeVarName :: Int -> String
typeVarName idx | idx < 0 = "t_[" ++ show idx ++ "]"
                | otherwise = (++) "t_" $ varNames !! idx

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
rsInfo v s = T.trace ("\n[RS_INFO] " ++ s) v

----------------------------------------------------------------
-- Utitility functions
----------------------------------------------------------------

-- | Accumulate left side of tuple in monad
mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM _ s1 [] = return (s1, [])
mapAccumLM f s1 (x:xs) = do 
  (s2, y) <- f s1 x
  fmap (y:) <$> mapAccumLM f s2 xs

-- | Map over a list with the corresponding index
mapWithIndex :: (Int -> a -> b) -> [a] -> [b] 
mapWithIndex f = go 0
    where go _ []     = []
          go n (x:xs) = f n x : go (n+1) xs 