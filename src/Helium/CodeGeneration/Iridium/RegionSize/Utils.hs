module Helium.CodeGeneration.Iridium.RegionSize.Utils
    (weakenIdx, strengthenIdx,
    rsShowType, typeRemoveQuants,
    indent, noTupleBreak,
    varNames, typeVarName, annVarName,
    rsError, rsInfo,
    mapAccumLM, mapWithIndex,
    ordNub, sortWith,
    cleanTUP, deSymbol
    ) where

import qualified Debug.Trace as T
import qualified Data.Set as S
import Data.Ord (comparing)
import Data.List

import Lvm.Core.Type

import GHC.Stack

----------------------------------------------------------------
-- De bruijn reinexing
----------------------------------------------------------------

type Depth = Int
type Index = Int

-- | Increase unbound indexes by subD
weakenIdx :: Int -> Depth -> Index -> Index
weakenIdx subD d idx = if idx > d -- If idx > d: var points outside of applicated term 
                        then idx + subD -- Reindex
                        else idx

-- | Increase unbound indexes by 1
strengthenIdx :: Depth -> Index -> Index
strengthenIdx d idx = if idx > d
                      then idx - 1 
                      else idx


----------------------------------------------------------------
-- LVM type utils
----------------------------------------------------------------

-- | Show a type with region size naming convention
rsShowType :: Type -> String
rsShowType = showType ((:) 't' <$> take 1000 varNames)

-- | Remove quantifications
typeRemoveQuants :: Type -> Type
typeRemoveQuants (TForall _ _ t) = typeRemoveQuants t
typeRemoveQuants t = t

----------------------------------------------------------------
-- Indenting
----------------------------------------------------------------

-- | Check if next tuple element should be on a newline
noTupleBreak :: String -> Bool
noTupleBreak (_:"") = True
noTupleBreak ('(':')':_) = True
noTupleBreak (c:_)  = c == 'ρ' || c == '⊥'
noTupleBreak ""     = False

-- | Indent a newline separated string
indent :: String -> String -> String
indent s = intercalate "\n" . map ((++) s) . splitOn '\n'

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
                | otherwise = (++) "t" $ varNames !! idx

-- | Get a type var name
annVarName :: Int -> String
annVarName idx | idx < 0 = "v$[" ++ show idx ++ "]"
               | otherwise = varNames !! idx

----------------------------------------------------------------
-- Console messages
----------------------------------------------------------------

rsError :: HasCallStack => String -> a
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

-- | Remove the word "TUP"
cleanTUP :: String -> String
cleanTUP [] = []
cleanTUP ('T':'U':'P': xs) = cleanTUP xs
cleanTUP (x:xs) = x : cleanTUP xs

-- | Nub bot O(nlogn)
ordNub :: (Ord a) => [a] -> [a]
ordNub = go S.empty
  where
    go _ []     = []
    go s (x:xs) =
      if x `S.member` s
      then go s xs
      else x : go (S.insert x s) xs

-- | Sort with selection
sortWith :: Ord o => (a -> o) -> [a] -> [a]
sortWith = sortBy . comparing

-- | Remove UTF8 symbols from a string
deSymbol :: String -> String
deSymbol [] = []
deSymbol ('λ':xs) = '\\':deSymbol xs
deSymbol ('ρ':xs) = 'r':'h':'o':'_':deSymbol xs
deSymbol ('π':xs) = 'p':'i':deSymbol xs
deSymbol ('∀':xs) = "forall " ++ deSymbol xs
deSymbol ('⊥':xs) = "bot" ++ deSymbol xs
deSymbol ('↦':xs) = "->" ++ deSymbol xs
deSymbol ('Ψ':xs) = "S" ++ deSymbol xs
deSymbol ('₀':xs) = '0':deSymbol xs
deSymbol ('₁':xs) = '1':deSymbol xs
deSymbol ('₂':xs) = '2':deSymbol xs
deSymbol ('₃':xs) = '3':deSymbol xs
deSymbol ('₄':xs) = '4':deSymbol xs
deSymbol ('₅':xs) = '5':deSymbol xs
deSymbol ('₆':xs) = '6':deSymbol xs
deSymbol ('₇':xs) = '7':deSymbol xs
deSymbol ('₈':xs) = '8':deSymbol xs
deSymbol ('₉':xs) = '9':deSymbol xs
deSymbol ('∞':xs) = 'X':deSymbol xs
deSymbol (x:xs) = x : deSymbol xs

