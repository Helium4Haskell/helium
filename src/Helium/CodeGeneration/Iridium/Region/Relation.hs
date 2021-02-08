{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Helium.CodeGeneration.Iridium.Region.Relation
  ( RelationConstraint, pattern Outlives
  , Relation, trivialConstraint, relationToConstraints, showRelationWith
  , relationFromTransitiveConstraints, relationFromConstraints
  , relationJoin, subRelation, relationIsEmpty, relationEmpty
  , relationWeaken, relationWeaken', relationStrengthen, relationStrengthen'
  , relationReindex, relationMultipleReindex, relationMultipleReindexMonotone, relationRestrict
  , outlives, outlivesSet, directlyOutlives, relationCollapse, relationFilter
  ) where

import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Utils
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Algorithms.Tim as V

import Data.Maybe
import Data.List
import Data.Word
import Data.Bits
import Data.Either

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

newtype RelationConstraint = OutlivesR Word64 deriving (Eq, Ord)
-- We assume that we need at most 32 bits for region variable indices

pattern Outlives :: RegionVar -> RegionVar -> RelationConstraint
pattern Outlives r1 r2 <- OutlivesR (destruct -> (r1, r2))
  where
    Outlives r1 r2 = OutlivesR (construct r1 r2)
{-# COMPLETE Outlives #-}

construct :: RegionVar -> RegionVar -> Word64
construct (RegionVar left) (RegionVar right) = shiftL (fromIntegral left) 32 .|. fromIntegral right

destruct :: Word64 -> (RegionVar, RegionVar)
destruct repr = (RegionVar $ fromIntegral $ shiftR repr 32, RegionVar $ fromIntegral $ repr .&. 0xFFFFFFFF)

instance Show RelationConstraint where
  showsPrec _ (r1 `Outlives` r2) s = show r1 ++ " ≥ " ++ show r2 ++ s
  showList = showListWith "⟦" "⟧" shows

trivialConstraint :: RelationConstraint -> Bool
trivialConstraint (RegionGlobal `Outlives` _) = True
trivialConstraint (_ `Outlives` RegionBottom) = True
trivialConstraint (x `Outlives` y) = x == y

newtype Relation = Relation (V.Vector Word64) deriving Eq
-- Relations are represented as a list of relation constraints, packed as a Word64.
-- The list should be sorted, the constraints should be transitive and not include
-- trivial constraints (as per function 'trivialConstraint').

instance Show Relation where
  show = show . relationToConstraints

showRelationWith :: (RegionVar -> String) -> Relation -> ShowS
showRelationWith showRegionVar = showListWith "⟦" "⟧" (\(Outlives x y) s -> showRegionVar x ++ " ≥ " ++ showRegionVar y ++ s) . relationToConstraints

instance Ord Relation where
  (<=) = subRelation

relationToConstraints :: Relation -> [RelationConstraint]
relationToConstraints (Relation vec) = map OutlivesR $ V.toList vec

-- Assumes that the input is transitive, sorted and doesn't includ trivial constraints.
relationFromTransitiveConstraints :: [RelationConstraint] -> Relation
relationFromTransitiveConstraints = Relation . V.fromList . map (\(OutlivesR repr) -> repr)

relationFromConstraints :: [RelationConstraint] -> Relation
relationFromConstraints constraints = makeTransitive initial initial
  where
    initial = V.modify V.sort $ V.fromList [ repr | c@(OutlivesR repr) <- constraints, not $ trivialConstraint c ]

relationEmpty :: Relation
relationEmpty = Relation V.empty

relationIsEmpty :: Relation -> Bool
relationIsEmpty (Relation vec) = V.null vec

-- Makes a relation transitive. 'edges' is the array of vectors which were added in the previous iteration of
-- the algorithm. We only need to search for two-hops starting with those edges.
-- TODO: if x >= global and y >= global, then add x>=y and y>=x
makeTransitive :: V.Vector Word64 -> V.Vector Word64 -> Relation
makeTransitive relation edges
  | V.length relation == V.length newRelation = Relation relation -- no new edges were found
  | otherwise = makeTransitive newRelation $ diff hops relation
  where
    hops = twoHops edges relation
    newRelation = merge relation hops

relationJoin :: Relation -> Relation -> Relation
relationJoin (Relation as) (Relation bs)
  | V.length as == 0 = Relation bs
  | V.length bs == 0 = Relation as
  | V.length initial == V.length relation = Relation initial -- No new edges/constraints were formed by merging these two relations
  | otherwise = makeTransitive relation (diff hops initial) -- Make the relation transitive
  where
    initial = merge as bs
    hops = twoHops as bs `merge` twoHops bs as
    relation = merge initial hops

subRelation :: Relation -> Relation -> Bool
subRelation (Relation as) (Relation bs) = subVector as bs

outlives :: Relation -> RegionVar -> RegionVar -> Bool
outlives (Relation vec) x y = trivialConstraint (Outlives x y) || binarySearch vec repr
  where
    OutlivesR repr = Outlives x y

-- Returns the regions which the specified region variable outlives, minus the ones of trivial constraints.
-- y \elem outlivesSet R x || trivialConstraint (Outlives x y) <=> outlives R x y
outlivesSet :: Relation -> RegionVar -> [RegionVar]
outlivesSet (Relation vec) x = case binarySearchRange vec repr1 repr2 of
  Nothing -> []
  Just (idx1, idx2) -> map (\repr -> let Outlives _ y = OutlivesR repr in y) $ V.toList $ V.slice idx1 (idx2 - idx1 + 1) vec
  where
    OutlivesR repr1 = Outlives x $ RegionVar 0
    OutlivesR repr2 = Outlives x $ RegionVar 0xFFFFFFFF

-- We say that region x directly outlives region y if outlivesSet(x) = outlivesSet(y) ∪ {y}.
directlyOutlives :: Relation -> RegionVar -> RegionVar -> Bool
directlyOutlives rel x y = outlives rel x y && go (outlivesSet rel x) (outlivesSet rel y)
  where
    go :: [RegionVar] -> [RegionVar] -> Bool
    go (a:as) bs
      | a == y = as == bs
    go (a:as) (b:bs)
      | a == b = go as bs
    go _ _ = False

-- Returns all two-hops starting with the first edge in 'as' and the second edge in 'bs'.
-- Assumes that both input arrays are sorted and returns a sorted array.
twoHops :: V.Vector Word64 -> V.Vector Word64 -> V.Vector Word64
twoHops as bs = V.concat $ group 0
  where
    -- Groups all RelationConstraints with the same left argument, and finds all two-hops starting there.
    group :: Int -> [V.Vector Word64]
    group idx
      | idx >= V.length as = []
    group idx = section : group idx'
      where
        Outlives r1 r2 = OutlivesR (as V.! idx)
        (section, idx') = go r1 (idx + 1) (hops r1 r2)

    -- Finds a (sorted) list of RelationConstraints with the given region variable as the left argument.
    --
    go :: RegionVar -> Int -> V.Vector Word64 -> (V.Vector Word64, Int)
    go !r1 !idx !accum
      | idx >= V.length as || r1 /= r1' = (accum, idx)
      | otherwise = go r1 (idx + 1) (merge accum hops') -- TODO: Use a tree reduction instead of a chained reduction, to let 'merge' operate on smaller arrays.
      where
        Outlives r1' r2 = OutlivesR (as V.! idx)
        hops' = hops r1 r2 -- TODO: Fuse 'V.map' and 'V.filter' into 'merge' to prevent the construction of the intermediate array.

    hops :: RegionVar -> RegionVar -> V.Vector Word64
    hops r1 r2 = case binarySearchRange bs repr1 repr2 of
      Nothing -> V.empty
      Just (idx1, idx2) -> V.filter (\repr -> not $ trivialConstraint $ OutlivesR repr) $ V.map (\repr -> let Outlives _ r3 = OutlivesR repr in let OutlivesR repr' = Outlives r1 r3 in repr') $ V.slice idx1 (idx2 - idx1 + 1) bs
      where
        OutlivesR repr1 = Outlives r2 $ RegionVar 0
        OutlivesR repr2 = Outlives r2 $ RegionVar 0xFFFFFFFF

relationReindex :: (RegionVar -> RegionVar) -> Relation -> Relation
relationReindex f (Relation vec) = Relation $ V.uniq $ V.modify V.sort $ V.mapMaybe g vec
  where
    g :: Word64 -> Maybe Word64
    g repr
      | trivialConstraint (Outlives x' y') = Nothing
      | otherwise = Just repr'
      where
        Outlives x y = OutlivesR repr
        x' = f x
        y' = f y
        OutlivesR repr' = Outlives x' y'

relationMultipleReindex :: (RegionVar -> [RegionVar]) -> Relation -> Relation
relationMultipleReindex f (Relation input) = Relation $ V.modify V.sort $ V.concatMap g input
  -- TODO: We could have a more optimized version that doesn't require re-sorting
  where
    g :: Word64 -> V.Vector Word64
    g repr
      | [r1'] <- r1s = V.fromList $ map (r1' `outlivesRepr`) r2s
      | [r2'] <- r2s = V.fromList $ map (`outlivesRepr` r2') r1s
      | otherwise = V.fromList $ zipWith outlivesRepr r1s r2s
      where
        Outlives r1 r2 = OutlivesR repr
        r1s = f r1
        r2s = f r2

    outlivesRepr :: RegionVar -> RegionVar -> Word64
    outlivesRepr r1 r2 = repr
      where
        OutlivesR repr = Outlives r1 r2

-- Function 'f' should be monotone:
--   x > y ==> forall x' in f x, y' in f y, x' > y'
-- Function 'f' should return a strictly increasing list
-- The substitution should not affect RegionGlobal and RegionBottom
relationMultipleReindexMonotone :: (RegionVar -> [RegionVar]) -> Relation -> Relation
relationMultipleReindexMonotone = relationMultipleReindex
  -- TODO: We could have a more optimized version that doesn't require re-sorting
 
relationWeaken :: Int -> Relation -> Relation
relationWeaken = relationWeaken' 0

-- The substitution function is monotone, so we don't have to sort again, nor we need to remove trivial constraints or make it transitive
relationWeaken' :: Int -> Int -> Relation -> Relation
relationWeaken' _ 0 relation = relation
relationWeaken' firstIdx k (Relation vec) = Relation $ V.map f vec
  where
    f repr = repr'
      where
        Outlives x y = OutlivesR repr
        x' = weakenRegionVar firstIdx k x
        y' = weakenRegionVar firstIdx k y
        OutlivesR repr' = Outlives x' y'

relationStrengthen :: Int -> Relation -> Maybe Relation
relationStrengthen = relationStrengthen' 0

-- The substitution function is monotone, so we don't have to sort again, nor we need to remove trivial constraints or make it transitive
relationStrengthen' :: Int -> Int -> Relation -> Maybe Relation
relationStrengthen' _ 0 relation = Just relation
relationStrengthen' firstIdx k (Relation vec) = Relation <$> V.mapM f vec
  where
    f repr = (\x' y' -> let OutlivesR repr' = Outlives x' y' in repr') <$> strengthenRegionVar firstIdx k x <*> strengthenRegionVar firstIdx k y
      where
        Outlives x y = OutlivesR repr

-- Removes the first 'k' variables (Debruijn indices) and strengthens the remaining variables.
-- Also returns a list of variables which were present on the left hand side of removed constraints.
relationRestrict :: Int -> Relation -> ([RegionVar], Relation)
relationRestrict 0 rel = ([], rel)
relationRestrict k rel@(Relation vec) = (mapMaybe h $ relationToConstraints rel, Relation $ V.mapMaybe f vec)
  where
    f repr = (\x' y' -> let OutlivesR repr' = Outlives x' y' in repr') <$> g x <*> g y
      where
        Outlives x y = OutlivesR repr
    g (RegionLocal idx)
      | idx < k = Nothing
      | otherwise = Just $ RegionVar $ idx - k
    g r = Just r

    h (Outlives x y)
      | Just x' <- g x -- This constraint is removed, but we need to signal that this variable was used.
      , Nothing <- g y = Just x'
      | otherwise = Nothing

relationFilter :: (RegionVar -> Bool) -> Relation -> Relation
relationFilter f (Relation vec) = Relation $ V.filter g vec
  where
    g repr = let Outlives x y = OutlivesR repr in f x && f y

relationFilter' :: (RegionVar -> Bool) -> [(RegionVar, a)] -> Relation -> Relation
relationFilter' canCollapse unifications = relationFilter (\x -> not (canCollapse x) || not (any ((== x) . fst) unifications))

-- 'canCollapse' and 'vars' should represent the same set of variables:
--   x `elem` vars ==> canCollapse x
relationCollapseBottom :: (RegionVar -> Bool) -> [RegionVar] -> Relation -> (([RegionVar], Relation), [(RegionVar, RegionVar)])
relationCollapseBottom canCollapse vars relation = case partitionEithers $ map f vars of
  ([], _) -> ((vars, relation), []) -- Fixpoint
  (unifications, vars') -> (unifications ++) <$> relationCollapseBottom canCollapse vars' (relationFilter' canCollapse unifications relation)
  where
    f :: RegionVar -> Either (RegionVar, RegionVar) RegionVar
    f x
      | [] <- outlivesSet relation x = Left (x, RegionBottom)
      | otherwise = Right x

-- 'canCollapse' and 'vars' should represent the same set of variables:
--   x `elem` vars ==> canCollapse x
relationCollapseCyclic :: (RegionVar -> Bool) -> [RegionVar] -> Relation -> ([RegionVar], Relation, [(RegionVar, RegionVar)])
relationCollapseCyclic canCollapse vars rel = (vars', relationFilter' canCollapse unifications rel, unifications)
  where
    (unifications, vars') = partitionEithers $ map f vars

    f :: RegionVar -> Either (RegionVar, RegionVar) RegionVar
    f x = case find (unify x) $ outlivesSet rel x of
      Just y -> Left (x, y)
      Nothing -> Right x

    unify :: RegionVar -> RegionVar -> Bool
    -- Unify a region with a region outside of the target range,
    -- or with a region variable with a higher index.
    -- The latter assures that we don't unify x with y and y with x.
    unify x@(RegionVar idxX) y@(RegionVar idxY) = (not (canCollapse y) || idxX < idxY) && outlives rel y x 

-- 'canCollapse' and 'vars' should represent the same set of variables:
--   x `elem` vars ==> canCollapse x
relationCollapseDirectOutlives :: (RegionVar -> Bool) -> [RegionVar] -> Relation -> (Relation, [(RegionVar, RegionVar)])
relationCollapseDirectOutlives canCollapse vars relation = case partitionEithers $ map f vars of
  ([], _) -> (relation, []) -- Fixpoint
  (unifications, vars') -> (unifications ++) <$> relationCollapseDirectOutlives canCollapse vars' (relationFilter' canCollapse unifications relation)

  where
    f :: RegionVar -> Either (RegionVar, RegionVar) RegionVar
    f x = case find (directlyOutlives relation x) $ outlivesSet relation x of
      Just y -> Left (x, y)
      Nothing -> Right x

-- 'canCollapse' and 'vars' should represent the same set of variables:
--   canCollapse x iff x `elem` vars
relationCollapse :: (RegionVar -> Bool) -> [RegionVar] -> Relation -> (Relation, [(RegionVar, RegionVar)]) -- Unifications may not be closed/idempotent, eg we need to recursively descend to find the substituted region var.
relationCollapse canCollapse vars1 relation1 = (relation4, bottomUnifications ++ cycleUnifications ++ directOutlivesUnifications)
  where
    ((vars2, relation2), bottomUnifications) = relationCollapseBottom canCollapse vars1 relation1

    (vars3, relation3, cycleUnifications) = relationCollapseCyclic canCollapse vars2 relation2

    (relation4, directOutlivesUnifications) = relationCollapseDirectOutlives canCollapse vars3 relation3


instance Semigroup Relation where
  (<>) = relationJoin

instance Monoid Relation where
  mempty = relationEmpty
