module Helium.Optimization.Annotations where

import Helium.Optimization.Utils

import Data.Set (Set)
import qualified Data.Set as Set

data Ann = AnnVar Int
         | AnnVal AnnValue
    deriving (Show, Eq, Ord)

type AnnValue = Set AnnPrim
data AnnPrim = Zero
             | One
             | Infinity
    deriving (Show, Eq, Ord)

freshAnn :: Fresh Ann
freshAnn = AnnVar <$> fresh

annToInt :: AnnPrim -> Int
annToInt Zero = 0
annToInt One = 1
annToInt Infinity = 2;

annFromInt :: Int -> AnnPrim
annFromInt 0 = Zero
annFromInt 1 = One
annFromInt _ = Infinity

(.+) :: AnnPrim -> AnnPrim -> AnnPrim
x .+ y = annFromInt $ annToInt x + annToInt y

{- Named Annotations -}
annBot', annZero', annOne', annW', annTop' :: AnnValue
annBot' = Set.empty
annZero' = Set.singleton Zero
annOne' = Set.singleton One
annW' = Set.singleton Infinity
annTop' = Set.fromList [Zero, One, Infinity]

annBot, annZero, annOne, annW, annTop :: Ann
annBot = AnnVal annBot'
annZero = AnnVal annZero'
annOne = AnnVal annOne'
annW = AnnVal annW'
annTop = AnnVal annTop'

{- Annotation Operations -}
annPlus :: AnnValue -> AnnValue -> AnnValue
annPlus a1 a2 = Set.fromList [x .+ y | x <- Set.toList a1, y <- Set.toList a2]

annUnion :: AnnValue -> AnnValue -> AnnValue
annUnion = Set.union

annTimes :: AnnValue -> AnnValue -> AnnValue
annTimes a1 a2 = Set.fromList [annFromInt (sum $ map annToInt y) | x <- Set.toList a1, y <- f (annToInt x) $ Set.toList a2]
  where f 0 _ = [[]]
        f _ [] = []
        f n y@(x:xs) = f n xs ++ map (x:) (f (n-1) y)

annCond :: AnnValue -> AnnValue -> AnnValue
annCond a1 a2 = Set.unions $ map (\x -> if x == Zero then annZero' else a2) $ Set.toList a1