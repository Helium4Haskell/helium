{-# LANGUAGE BangPatterns #-}

module Helium.CodeGeneration.Iridium.Region.Utils where

import System.IO
import Lvm.Common.Id
import Lvm.Core.Type
import Data.IntMap (IntMap)
import Data.Word
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Vector.Unboxed as V

typeDependencies :: Bool -> Type -> [Id]
typeDependencies inFunctions tp = dependencies tp []
  where
    dependencies :: Type -> [Id] -> [Id]
    dependencies (TAp (TAp (TCon TConFun) t1) t2) accum
      | inFunctions = dependencies t1 $ dependencies t2 accum
      | otherwise = accum
    dependencies (TAp t1 t2) accum = dependencies t1 $ dependencies t2 accum
    dependencies (TForall _ _ t1) accum = dependencies t1 accum
    dependencies (TStrict t1) accum = dependencies t1 accum
    dependencies (TCon (TConDataType name)) accum = name : accum
    dependencies (TCon (TConTypeClassDictionary name)) accum = dictionaryDataTypeName name : accum
    dependencies _ accum = accum

showSubscript :: Int -> String
showSubscript idx
  | idx == 0 = take 1 numbersSubscript
  | idx > 0 = showInt idx ""
  | otherwise = '₋' : showInt (-idx) ""
  where
    numbersSubscript = "₀₁₂₃₄₅₆₇₈₉"
    showInt :: Int -> String -> String
    showInt value accum
      | rest == 0 = accum'
      | otherwise = showInt rest accum'
      where
        accum' = char : accum
        digit = value `mod` 10
        char = numbersSubscript !!! digit
        rest = value `div` 10

showListWith :: String -> String -> (a -> ShowS) -> [a] -> ShowS
showListWith open close _ [] s = open ++ close ++ s
showListWith open close f (x:xs) s = open ++ f x (go xs)
  where
    go [] = close ++ s
    go (y:ys) = ", " ++ f y (go ys)

showsIntercalate :: (a -> ShowS) -> String -> [a] -> ShowS
showsIntercalate _ _ [] s = s
showsIntercalate f sep (x:xs) s = f x (go xs)
  where
    go [] = s
    go (y:ys) = sep ++ f y (go ys)

debugLog :: Maybe Handle -> String -> IO ()
debugLog Nothing _ = return ()
debugLog (Just h) string = hPutStrLn h string

tryIndex :: [a] -> Int -> Maybe a
tryIndex [] _ = Nothing
tryIndex (a:_) 0 = Just a
tryIndex (_:as) n = tryIndex as (n - 1)

(!!!) :: Show a => [a] -> Int -> a
(!!!) as idx = case tryIndex as idx of
  Just a -> a
  Nothing -> error $ "index: cannot find index " ++ show idx ++ " in " ++ show as

showIntMap :: Show a => IntMap a -> String
showIntMap m = IntMap.toList m >>= showElem
  where
    showElem (key, value) = "\n" ++ show key ++ " = " ++ show value

binarySearch :: V.Vector Word64 -> Word64 -> Bool
binarySearch vec q
  | size == 0  = False
  | q < head'  = False
  | q == head' = True
  | q > last'  = False
  | q == last' = True
  | otherwise  = go 0 (size - 1)
  where
    size = V.length vec
    head' = V.head vec
    last' = vec V.! (size - 1)

    -- Invariants:
    --   vec !! lower < q
    --   q < vec !! upper
    --   upper > lower
    go :: Int -> Int -> Bool
    go lower upper
      | upper - lower <= 1 = False
      | otherwise = case compare (vec V.! mid) q of
          LT -> go mid upper
          GT -> go lower mid
          EQ -> True
      where
        mid = (lower + upper) `div` 2

-- Returns whether the number was found and the index of the last element equal to or smaller than
-- the queried value, or -1 if that doesn't exist.
binarySearchIndexBefore :: V.Vector Word64 -> Word64 -> (Bool, Int)
binarySearchIndexBefore vec q
  | size == 0  = (False, -1)
  | q < head'  = (False, -1)
  | q == head' = (True, 0)
  | q > last'  = (False, size - 1)
  | q == last' = (True, size - 1)
  | otherwise  = go 0 (size - 1)
  where
    size = V.length vec
    head' = V.head vec
    last' = vec V.! (size - 1)

    -- Invariants:
    --   vec !! lower < q
    --   q < vec !! upper
    --   upper > lower
    go :: Int -> Int -> (Bool, Int)
    go lower upper 
      | upper - lower <= 1 = (False, lower)
      | otherwise = case compare (vec V.! mid) q of
          LT -> go mid upper
          GT -> go lower mid
          EQ -> (True, mid)
      where
        mid = (lower + upper) `div` 2

-- Returns whether the number was found and the index of the first element equal to or larger than
-- the queried value, or the length of the input vector if that doesn't exist.
binarySearchIndexAfter :: V.Vector Word64 -> Word64 -> (Bool, Int)
binarySearchIndexAfter vec q = case binarySearchIndexBefore vec q of
  (True, idx)  -> (True, idx)
  (False, idx) -> (False, idx + 1)

-- Returns the indices of the first element larger than q1 and the last element smaller than q2
binarySearchRange :: V.Vector Word64 -> Word64 -> Word64 -> Maybe (Int, Int)
binarySearchRange vec q1 q2
  | upper > lower = Nothing
  | otherwise = Just (lower, upper)
  where
    (_, lower) = binarySearchIndexAfter vec q1
    (_, upper) = binarySearchIndexBefore vec q2

-- Takes two sorted vectors which do not contain duplicate values,
-- and returns a sorted vector containing all values from the two input arrays.
-- If a value was present in both input arrays, it will only be present once
-- in the output vector.
merge :: V.Vector Word64 -> V.Vector Word64 -> V.Vector Word64
merge as bs
  | V.length as == 0 = bs
  | V.length bs == 0 = as
  | otherwise = V.unfoldrN (V.length as + V.length bs) f (Just 0, Just 0)
  where
    f :: (Maybe Int, Maybe Int) -> Maybe (Word64, (Maybe Int, Maybe Int))
    f (Nothing,   Nothing  ) = Nothing
    f (Just idxA, Nothing  ) = Just (as V.! idxA, (incA idxA, Nothing))
    f (Nothing,   Just idxB) = Just (bs V.! idxB, (Nothing, incB idxB))
    f (Just idxA, Just idxB)
      | a == b    = Just (a, (incA idxA, incB idxB))
      | a < b     = Just (a, (incA idxA, Just idxB))
      | otherwise = Just (b, (Just idxA, incB idxB))
      where
        a = as V.! idxA
        b = bs V.! idxB

    incA :: Int -> Maybe Int
    incA idx
      | idx >= V.length as - 1 = Nothing
      | otherwise = Just $ idx + 1

    incB :: Int -> Maybe Int
    incB idx
      | idx >= V.length bs - 1 = Nothing
      | otherwise = Just $ idx + 1

-- Returns the elements of the first vector which are not present in the second.
-- Assumes that both vectors are sorted and do not contain duplicates.
diff :: V.Vector Word64 -> V.Vector Word64 -> V.Vector Word64
diff as bs
  | V.length as == 0 = as
  | V.length bs == 0 = as
  | otherwise = V.unfoldrN (V.length as) f (Just 0, Just 0)
  where
    f :: (Maybe Int, Maybe Int) -> Maybe (Word64, (Maybe Int, Maybe Int))
    f (Nothing  , _) = Nothing
    f (Just idxA, Nothing  ) = Just (as V.! idxA, (incA idxA, Nothing))
    f (Just idxA, Just idxB)
      | a == b    = f (incA idxA, incB idxB)
      | a < b     = Just (a, (incA idxA, Just idxB))
      | otherwise = f (Just idxA, incB idxB)
      where
        a = as V.! idxA
        b = bs V.! idxB

    incA :: Int -> Maybe Int
    incA idx
      | idx >= V.length as - 1 = Nothing
      | otherwise = Just $ idx + 1

    incB :: Int -> Maybe Int
    incB idx
      | idx >= V.length bs - 1 = Nothing
      | otherwise = Just $ idx + 1

-- Given two sorted vectors with no duplicates, checks whether all elements of the first vector are also present in the second.
subVector :: V.Vector Word64 -> V.Vector Word64 -> Bool
subVector as bs = go 0 0
  where
    go :: Int -> Int -> Bool
    go !idxA !idxB
      | idxA >= V.length as = True -- Traversed all elements
      | idxB >= V.length bs = False -- Elements are remaining in 'as', but they are not present in 'bs'
      | a == b = go (idxA + 1) (idxB + 1)
      | a > b = go idxA (idxB + 1)
      | otherwise = False
      where
        a = as V.! idxA
        b = bs V.! idxB

weakenIndex :: Int -> Int -> Int -> Int
weakenIndex first k idx
  | idx < first = idx
  | otherwise = idx + k

strengthenIndex :: Int -> Int -> Int -> Maybe Int
strengthenIndex first k idx
  | idx < first = Just idx
  | idx < first + k = Nothing
  | otherwise = Just $ idx - k

nubSorted :: Eq a => [a] -> [a]
nubSorted [] = []
nubSorted (x : xs) = x : go x xs
  where
    go _ [] = []
    go y (z : zs)
      | y == z = go y zs
      | otherwise = z : go z zs

mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM _ s1 [] = return (s1, [])
mapAccumLM f s1 (x:xs) = do 
  (s2, y) <- f s1 x
  fmap (y:) <$> mapAccumLM f s2 xs
