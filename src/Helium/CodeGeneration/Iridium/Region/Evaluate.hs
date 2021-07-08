{-# LANGUAGE TupleSections #-}

module Helium.CodeGeneration.Iridium.Region.Evaluate
  ( simplify, simplifyFixEscape, weakSimplify, afixEscape
  , strengthen, weaken, annotationRestrict
  ) where

import Control.Applicative
import Data.Maybe
import Data.List

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Utils

import Debug.Trace

simplify :: DataTypeEnv -> Annotation -> Annotation
-- 'join' and 'afix' reduce a value fully, no need to recurse on the sub-annotations
simplify env annotation@AJoin{} = join False env annotation
simplify env (AFix a1 s a2) = afix False env (a1, s, a2)
simplify env annotation = case weakSimplifyStep env annotation of
  (True , annotation') -> nested annotation'
  (False, annotation') -> simplify env annotation'
  where
    nested (ALam argSort regionSort lifetime body)
      | ABottom s <- body' = ABottom (SortFun argSort regionSort lifetime s)
      | ATop s    <- body' = ATop    (SortFun argSort regionSort lifetime s)
      | AApp f (AVar (AnnotationVar 0)) regions lifetime' <- body'
      , lifetime == lifetime'
      , regions == regionSortToVars 0 regionSort
      , Just f' <- strengthen 0 1 (regionSortSize regionSort) f = f' -- eta reduction
      | otherwise = ALam argSort regionSort lifetime body'
      where
        body' = simplify env body
    nested (AForall q body)
      | ABottom s <- body' = ABottom (SortForall q s)
      | ATop s    <- body' = ATop    (SortForall q s)
      | AInstantiate a (TVar 0) <- body'
      , Just a' <- strengthen 1 0 0 a = a' -- eta reduction of quantification
      | otherwise = AForall q body'
      where
        body' = simplify env body
    nested AJoin{} = error "simplify: AJoin is not properly simplified"
    nested (AInstantiate a tp) = AInstantiate (nested a) tp -- 'a' is already weakly normalized.
    nested (AApp a1 a2 r lc) = AApp (nested a1) (simplify env a2) r lc -- 'a1' is already weakly normalized.
    nested (ATuple as) = tuple as
    nested (AProject a idx) = AProject (nested a) idx -- 'a' is already weakly normalized.
    nested a@AVar{} = a
    nested a@ARelation{} = a
    nested a@ABottom{} = a
    nested a@ATop{} = a
    nested a@AFix{} = a
    nested AFixEscape{} = error "simplify: AFixEscape is not properly simplified"

    tuple :: [Annotation] -> Annotation
    tuple annotations
      | null fixpoints = ATuple annotations'
      | otherwise = AFix fixpointF fixpointSort fixpointG
      where
        annotations' = simplify env <$> annotations
        (fixpoints, parts) = gatherFixpoints annotations'

        singleFixpoint
          | [_] <- fixpoints = True
          | otherwise = False

        fixpointSort
          | [(s, _)] <- fixpoints = s
          | otherwise = SortTuple $ map (\(s, _) -> s) fixpoints

        fixpointF = ALam fixpointSort RegionSortUnit LifetimeContextAny $ ATuple $ map fixpointFBody parts
        fixpointFBody (Right a) = weaken 0 1 0 a
        fixpointFBody (Left (idx, f)) = AApp (weaken 0 1 0 f) (if singleFixpoint then AVar (AnnotationVar 0) else AProject (AVar $ AnnotationVar 0) idx) (RegionVarsTuple []) LifetimeContextAny

        fixpointG
          | [(_, g)] <- fixpoints = g
          | otherwise = ALam fixpointSort RegionSortUnit LifetimeContextAny $ ATuple
            $ zipWith (\(_, g) i -> AApp (weaken 0 1 0 g) (AProject (AVar $ AnnotationVar 0) i) (RegionVarsTuple []) LifetimeContextAny) fixpoints [0..]

-- Same as 'simplify', but assumes that the expression is an AFixEscape.
-- Returns the substitution found in the escape check.
simplifyFixEscape :: DataTypeEnv -> Annotation -> [([Bool], RegionVar -> RegionVar, Annotation)]
simplifyFixEscape env (AFixEscape rs fs) = afixEscape env rs fs
simplifyFixEscape _ _ = error "simplifyFixEscape: Expected AFixEscape"

-- Given a list of annotations, extracts the list of fixpoints, represented by the sorts and body, and a list of all parts,
-- as a non-recursive term (Right) or part of the fixpoint (Left, with the index of the fixpoint and function 'f' before the fixpoint).
gatherFixpoints :: [Annotation] -> ([(Sort, Annotation)], [Either (Int, Annotation) Annotation])
gatherFixpoints = go 0
  where
    go :: Int -> [Annotation] -> ([(Sort, Annotation)], [Either (Int, Annotation) Annotation])
    go _ [] = ([], [])
    go k (AFix f s g : as) = ((s, g) : fixpoints', Left (k, f) : parts')
      where
        (fixpoints', parts') = go (k + 1) as
    go k (a : as) = (fixpoints', Right a : parts')
      where
        (fixpoints', parts') = go k as

-- Simplifies and widens an annotation to a form without 
-- widen :: DataTypeEnv -> Annotation -> Annotation
-- widen = undefined

-- Widens an already simplified annotation
-- widen' :: DataTypeEnv -> Annotation -> Annotation

-- Simplifies (at least) the head of a term. Similar to weak head normal form,
-- but it might leave some fixpoints in the output and thus is not a normal form.
weakSimplify :: DataTypeEnv -> Annotation -> Annotation
weakSimplify env annotation = case weakSimplifyStep env annotation of
  (True, a) -> a
  (False, a) -> weakSimplify env a

weakSimplifyStep :: DataTypeEnv -> Annotation -> (IsWeakSimplified, Annotation)
weakSimplifyStep env annotation = case annotation of
  ALam{} -> (True, annotation)
  AForall{} -> (True, annotation)
  ATop SortRelation -> (True, ABottom SortRelation) -- Top and bottom of SortRelation are both an empty relation
  ATop _ -> (True, annotation)
  ABottom _ -> (True, annotation)
  ARelation{} -> (True, annotation)
  ATuple{} -> (True, annotation)
  AVar{} -> (True, annotation)

  AJoin{} -> (True, join True env annotation)

  AFix a1 s a2 -> (True, afix False env (a1, s, a2))
  AFixEscape rs fs -> 
    let
      as = afixEscape env rs fs
    in
      (False, ATuple $ map (\(_, _, a) -> a) as)

  AInstantiate a tp -> instantiate env a tp
  AApp a1 a2 r lc -> apply env a1 a2 r lc

  AProject as idx -> project env as idx


type IsWeakSimplified = Bool

weaken :: Int -> Int -> Int -> Annotation -> Annotation
weaken 0 0 0 = id
weaken typeK annotationK regionK = transform 0 0 0
  where
    transform :: Int -> Int -> Int -> Annotation -> Annotation
    transform forallCount lambdaCount regionCount a = case a of
      AFix a1 s a2 -> AFix (transform' a1) (transformSort s) (transform' a2)
      AFixEscape rs fs -> AFixEscape rs $ map (\(a, s, f) -> (a, s, transform' f)) fs
      AForall q a1 -> AForall q $ transform (forallCount + 1) lambdaCount regionCount a1
      ALam s regionSort lifetime a1 -> ALam (transformSort s) (transformRegionSort regionSort) lifetime $ transform forallCount (lambdaCount + 1) (regionCount + regionSortSize regionSort) a1
      AInstantiate a1 tp -> AInstantiate (transform' a1) (transformType tp)
      AApp a1 a2 rs lc -> AApp (transform' a1) (transform' a2) (transformRegionVars rs) lc
      ATuple as -> ATuple $ transform' <$> as
      AProject a1 idx -> AProject (transform' a1) idx
      AVar (AnnotationVar idx) -> AVar $ AnnotationVar $ weakenIndex lambdaCount annotationK idx
      ARelation rel -> ARelation $ relationWeaken' regionCount regionK rel
      ATop s -> ATop $ transformSort s
      ABottom s -> ABottom $ transformSort s
      AJoin a1 a2 -> AJoin (transform' a1) (transform' a2)
      where
        transform' = transform forallCount lambdaCount regionCount
        transformType = typeReindex (weakenIndex forallCount typeK)
        transformSort = sortWeaken' forallCount typeK
        transformRegionSort = regionSortWeaken' forallCount typeK
        transformRegionVars = mapRegionVars (weakenRegionVar regionCount regionK)

strengthen :: Int -> Int -> Int -> Annotation -> Maybe Annotation
strengthen 0 0 0 = Just
strengthen typeK annotationK regionK = transform 0 0 0
  where
    transform :: Int -> Int -> Int -> Annotation -> Maybe Annotation
    transform forallCount lambdaCount regionCount a = case a of
      AFix a1 s a2 -> AFix <$> transform' a1 <*> transformSort s <*> transform' a2
      AFixEscape rs fs -> AFixEscape rs <$> traverse (\(a, s, f) -> (a, s, ) <$> transform' f) fs
      AForall q a1 -> AForall q <$> transform (forallCount + 1) lambdaCount regionCount a1
      ALam s regionSort lifetime a1 -> ALam <$> transformSort s <*> transformRegionSort regionSort <*> Just lifetime <*> transform forallCount (lambdaCount + 1) (regionCount + regionSortSize regionSort) a1
      AInstantiate a1 tp -> AInstantiate <$> transform' a1 <*> transformType tp
      AApp a1 a2 rs lc -> AApp <$> transform' a1 <*> transform' a2 <*> transformRegionVars rs <*> Just lc
      ATuple as -> ATuple <$> traverse transform' as
      AProject a1 idx -> (`AProject` idx) <$> transform' a1
      AVar (AnnotationVar idx) -> AVar . AnnotationVar <$> strengthenIndex lambdaCount annotationK idx
      ARelation rel -> ARelation <$> relationStrengthen' regionCount regionK rel
      ATop s -> ATop <$> transformSort s
      ABottom s -> ABottom <$> transformSort s
      AJoin a1 a2 -> AJoin <$> transform' a1 <*> transform' a2
      where
        transform' = transform forallCount lambdaCount regionCount
        transformType
          | typeK == 0 = Just
          | otherwise = typeReindexM (strengthenIndex forallCount typeK)
        transformSort = sortStrengthen' forallCount typeK
        transformRegionSort = regionSortStrengthen' forallCount typeK
        transformRegionVars = mapRegionVarsM (strengthenRegionVar regionCount regionK)

instantiate :: DataTypeEnv -> Annotation -> Type -> (IsWeakSimplified, Annotation)
instantiate dataTypeEnv annotation tp = instantiate' False annotation
  where
    instantiate' :: IsWeakSimplified -> Annotation -> (IsWeakSimplified, Annotation)
    instantiate' simplified (AJoin a1 a2) = (False, AJoin (snd $ instantiate' simplified a1) (snd $ instantiate' simplified a2))
    instantiate' _ (ATop s) = (True, ATop $ sortInstantiate dataTypeEnv s tp)
    instantiate' _ (AApp (ATop (SortFun s rs lc s')) a regions lc')
      = (False, AApp (ATop $ SortFun s rs lc $ sortInstantiate dataTypeEnv s' tp) a regions lc')
    instantiate' _ (ABottom s) = (True, ABottom $ sortInstantiate dataTypeEnv s tp)
    instantiate' _ (AForall _ a) = (False, transform 0 emptyEnv 0 a)
    instantiate' _ (AFix a1 s a2) = (False, AFix (mapInFunction (transform 0 emptyEnv 0) s a1) s a2)
    instantiate' _ (ARelation _) = error "Helium.CodeGeneration.Iridium.Region.Evaluate: sort mismatch, cannot instantiate a relation"
    instantiate' False a = uncurry instantiate' $ weakSimplifyStep dataTypeEnv a
    instantiate' True a = (True, AInstantiate a tp)

    -- Note that the values (region vars) in the environment nor the keys are RegionGlobal or RegionBottom,
    -- and that the RegionVars are Debruijn levels instead of indices
    transform :: Int -> Env RegionVars -> Int -> Annotation -> Annotation
    transform forallCount env newEnvSize a = case a of
      AFix a1 s a2 -> AFix (transform' a1) (transformSort s) $ transform' a2
      AFixEscape rs fs -> AFixEscape (transformRegionSort rs) $ map (\(a, s, f) -> (a, transformSort s, transform' f)) fs
      AForall q a1 -> AForall q $ transform (forallCount + 1) env newEnvSize a1
      ALam s rs lifetime a1 ->
        let
          s' = transformSort s
          rs' = transformRegionSort rs
          (env', newEnvSize') = regionVarMapping rs rs' env newEnvSize
        in
          ALam s' rs' lifetime $ transform forallCount env' newEnvSize' a1
      AInstantiate a1 tp1 -> AInstantiate (transform' a1) (transformType tp1)
      AApp a1 a2 r lc -> AApp (transform' a1) (transform' a2) (transformRegions r) lc
      ATuple as -> ATuple $ transform' <$> as
      AProject a1 idx -> AProject (transform' a1) idx
      AVar var -> AVar var
      ARelation rel -> arelation $ relationMultipleReindexMonotone (flattenRegionVars . transformRegions . RegionVarsSingle) rel
      ATop s -> ATop $ transformSort s
      ABottom s -> ABottom $ transformSort s
      AJoin a1 a2 -> AJoin (transform' a1) (transform' a2)
      where
        transform' = transform forallCount env newEnvSize
        transformType = typeSubstitute forallCount (typeWeaken forallCount tp)
        transformSort = sortSubstitute dataTypeEnv forallCount tp
        transformRegionSort = regionSortSubstitute dataTypeEnv forallCount tp

        transformRegion :: RegionVar -> RegionVars
        transformRegion (RegionLocal idx)
          | idx >= envSize env = RegionVarsSingle $ RegionLocal $ idx - envSize env + newEnvSize
          | otherwise = mapRegionVars (\(RegionVar level) -> RegionVar $ newEnvSize - 1 - level) $ envFind idx env
        transformRegion r = RegionVarsSingle r -- global or bottom

        transformRegions :: RegionVars -> RegionVars
        transformRegions = bindRegionVars transformRegion

    regionVarMapping :: RegionSort -> RegionSort -> Env RegionVars -> Int -> (Env RegionVars, Int)
    regionVarMapping _ RegionSortMonomorphic   env newEnvSize
      = (envPush (RegionVarsSingle $ RegionVar newEnvSize) env, newEnvSize + 1)
    regionVarMapping _ RegionSortPolymorphic{} env newEnvSize
      = (envPush (RegionVarsSingle $ RegionVar newEnvSize) env, newEnvSize + 1)
    regionVarMapping RegionSortUnit RegionSortUnit env newEnvSize
      = (env, newEnvSize)
    regionVarMapping (RegionSortTuple (x:xs)) (RegionSortTuple (y:ys)) env newEnvSize
      = regionVarMapping (RegionSortTuple xs) (RegionSortTuple ys) env' newEnvSize'
      where
        (env', newEnvSize') = regionVarMapping x y env newEnvSize
    regionVarMapping RegionSortPolymorphic{} rs env newEnvSize
      = (envPush vars env, newEnvSize')
      where
        (newEnvSize', vars) = regionSortToLevels newEnvSize rs
    regionVarMapping (RegionSortForall _ x) (RegionSortForall _ y) env newEnvSize = regionVarMapping x y env newEnvSize
    regionVarMapping _ _ _ _ = error "Illegal region var instantiation"

apply :: DataTypeEnv -> Annotation -> Annotation -> RegionVars -> LifetimeContext -> (IsWeakSimplified, Annotation)
apply env annotation argument argumentRegion lc
  | AFix a1 s a2 <- argument' = (False, AFix (mapInFunction (\a -> AApp (weaken 0 1 0 annotation) a argumentRegion lc) s a1) s a2)
  | otherwise =
    let
      (isWeakSimplified, hasTopAp, annotation') = apply' False annotation
    in
      case hasTopAp of
        Just (s, rs, lc, s') -> (False, AJoin annotation' $ snd $ topApplication s rs argument' argumentRegion lc s')
        Nothing -> (isWeakSimplified, annotation')
  where
    apply' :: IsWeakSimplified -> Annotation -> (IsWeakSimplified, Maybe (Sort, RegionSort, LifetimeContext, Sort), Annotation)
    apply' simplified (AJoin a1 a2) = (False, hasTopAp1 <|> hasTopAp2, AJoin a1' a2')
      where
        (_, hasTopAp1, a1') = apply' simplified a1
        (_, hasTopAp2, a2') = apply' simplified a2
    apply' _ (ABottom s) = case s of
      SortFun _ _ _ s' -> (True, Nothing, ABottom s')
      _ -> error $ "Helium.CodeGeneration.Iridium.Region.Annotation.apply: Bottom has wrong sort: " ++ showSort [] s ""
    apply' _ (AApp (ATop s) a1 regions lc) = case s of
      SortFun sArg1 rs1 lc1 (SortFun sArg2 rs2 lc2 sReturn) ->
        ( False
        , Just (sArg2, rs2, lc2, sReturn)
        , AApp (ATop $ SortFun sArg1 rs1 lc1 sReturn) a1 regions lc
        )
      _ -> error $ "Helium.CodeGeneration.Iridium.Region.Annotation.apply: Top application has wrong sort: " ++ showSort [] s ""
    apply' _ (ALam _ rs _ body) = (False, Nothing, substitute (regionVarMapping rs argumentRegion []) 0 0 0 body)
    apply' simplified (AFix a1 s a2) = (False, Nothing, AFix (mapInFunction (\a1' -> snd $ apply env a1' (weaken 0 1 0 argument) argumentRegion lc) s a1) s a2) -- Start with lambdaCount=1, as mapInFunction also creates a lambda. This lambda does not have region arguments.
    apply' _ (ATop (SortFun s rs lc s')) = (isWeakSimplified, Nothing, a)
      where
        (isWeakSimplified, a) = topApplication s rs argument' argumentRegion lc s'
    apply' False annotation' = uncurry apply' $ weakSimplifyStep env annotation'
    apply' True  annotation' = (True, Nothing, AApp annotation' argument argumentRegion lc)
 
    -- TODO: Rewrite with zipFlattenRegionVars?
    regionVarMapping :: RegionSort -> RegionVars -> [RegionVar] -> [RegionVar]
    regionVarMapping (RegionSortForall _ rs)    vars                         accum = regionVarMapping rs vars accum
    regionVarMapping rs                         (RegionVarsSingle var)       accum = map (const var) (flattenRegionVars $ regionSortToVars 0 rs) ++ accum
    regionVarMapping RegionSortUnit             (RegionVarsTuple [])         accum = accum
    regionVarMapping (RegionSortTuple (rs:rss)) (RegionVarsTuple (var:vars)) accum = regionVarMapping rs var $ regionVarMapping (RegionSortTuple rss) (RegionVarsTuple vars) accum
    regionVarMapping rs vars _ = error $ "Helium.CodeGeneration.Iridium.Region.Evaluate.apply: region sort mismatch:\n" ++ showRegionSort [] rs "" ++ "\n" ++ show vars ++ "\n" ++ show (AApp annotation argument argumentRegion lc)

    argument' = simplify env argument

    substitute :: [RegionVar] -> Int -> Int -> Int -> Annotation -> Annotation
    substitute regions forallCount lambdaCount regionArgCount annotation = case annotation of
      AFix a1 s a2 -> AFix (go a1) s (go a2)
      AFixEscape rs fs -> AFixEscape rs $ map (\(a, s, f) -> (a, s, go f)) fs

      AForall q a -> AForall q $ substitute regions (forallCount + 1) lambdaCount regionArgCount a
      ALam sort regionSort lifetime a -> ALam sort regionSort lifetime $ substitute regions forallCount (lambdaCount + 1) (regionArgCount + regionSortSize regionSort) a

      AInstantiate a tp -> AInstantiate (go a) tp
      AApp a1 a2 regions' lc' -> AApp (go a1) (go a2) (mapRegionVars substituteRegion regions') lc'

      ATuple as -> ATuple $ map go as
      AProject a idx -> AProject (go a) idx

      AVar (AnnotationVar idx)
        | idx <  lambdaCount -> AVar $ AnnotationVar idx
        | idx == lambdaCount -> weaken forallCount lambdaCount regionArgCount argument'
        | otherwise          -> AVar $ AnnotationVar $ idx - 1

      ARelation relation -> arelation $ relationReindex substituteRegion relation

      ABottom s -> ABottom s
      ATop s -> ATop s
      AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = substitute regions forallCount lambdaCount regionArgCount
        argumentRegionSize = length regions
        substituteRegion (RegionLocal idx)
          | idx < regionArgCount = RegionLocal idx
          | idx < regionArgCount + argumentRegionSize = weakenRegionVar 0 regionArgCount $ regions !! (regionArgCount + argumentRegionSize - idx - 1) -- TODO: This line is probably not correct
          | otherwise = RegionLocal $ idx - argumentRegionSize
        substituteRegion r = r

project :: DataTypeEnv -> Annotation -> Int -> (IsWeakSimplified, Annotation)
project env annotation idx = f False annotation
  where
    f _ (ATuple as) = case tryIndex as idx of
      Just a -> (False, a)
      Nothing -> error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Index out of bounds"
    f simplified (AJoin a1 a2) = (False, AJoin (snd $ f simplified a1) (snd $ f simplified a2))
    f _ (AFix a1 s a2) = (False, AFix (mapInFunction (\a -> AProject a idx) s a1) s a2)
    f _ (ABottom (SortTuple sorts)) = case tryIndex sorts idx of
      Just s -> (True, ABottom s)
      Nothing -> error $ "Helium.CodeGeneration.Iridium.Region.Annotation.project: Bottom: Index out of bounds: " ++ show idx ++ " / " ++ show (length sorts)
    f _ (ATop (SortTuple sorts)) = case tryIndex sorts idx of
      Just s -> (True, ABottom s)
      Nothing -> error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Top: Index out of bounds"
    f _ (AApp (ATop (SortFun s rs lc (SortTuple sorts))) a regions lc') = case tryIndex sorts idx of
      Just s' -> (False, AApp (ATop $ SortFun s rs lc s') a regions lc')
      Nothing -> error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Top application: Index out of bounds"
    f _ a
      | Just a' <- fTop a = (False, a')
    f True a = (True, AProject a idx)
    f False a = uncurry f $ weakSimplifyStep env a

    fTop :: Annotation -> Maybe Annotation
    fTop (AApp a1 a2 rs lc) = (\a' -> AApp a' a2 rs lc) <$> fTop a1
    fTop (AInstantiate a tp) = (`AInstantiate` tp) <$> fTop a
    fTop (ATop s) = Just $ ATop $ projectSort s
    fTop _ = Nothing

    projectSort (SortForall q s) = SortForall q $ projectSort s
    projectSort (SortFun s1 rs lc s2) = SortFun s1 rs lc $ projectSort s2
    projectSort (SortTuple sorts) = case tryIndex sorts idx of
      Just s -> s
      Nothing -> error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Top: Index out of bounds"
    projectSort s = error $ "Helium.CodeGeneration.Iridium.Region.Annotation.project: Top: Illegal sort: " ++ showSort [] s "" ++ ", index " ++ show idx

join :: Bool -> DataTypeEnv -> Annotation -> Annotation
join weak env annotation = group $ gather False annotation []
  where
    group :: [Annotation] -> Annotation
    group annotations
      | Just top <- find isTop extremals = top
      | null parts = head extremals -- Should be bottom
      | Just fixpoint <- groupFixpoints parts = (if weak then weakSimplify else simplify) env fixpoint
      | Just (AForall q _) <- find isForall parts
        = AForall q $ deep
          $ [ a | AForall _ a <- parts ]
          ++ map (\a -> AInstantiate (weaken 1 0 0 a) (TVar 0)) (filter (not . isForall) parts)
      | Just (ALam s rs lc _) <- find isLam parts
        = ALam s rs lc $ deep
          $ [ a | ALam _ _ _ a <- parts ]
          ++ map (\a -> AApp (weaken 0 1 (regionSortSize rs) a) (AVar $ AnnotationVar 0) (regionSortToVars 0 rs) lc) (filter (not . isLam) parts)
      | hd:_ <- tuples
      , tuples' <- map (\a -> zipWith (\_ idx -> AProject a idx) hd [0..]) $ filter (not . isTuple) parts
        = ATuple $ map deep $ transpose (tuples ++ tuples')
      | Just g <- grouped = foldr1 AJoin $ g : others
      | otherwise = foldr1 AJoin others
      where
        (extremals, parts) = partition isExtreme annotations
        tuples = [as | ATuple as <- parts]
        relations = [r | ARelation r <- parts]
        others = nubSorted $ sort $ filter (\a -> not $ isRelation a) parts

        -- Group relations
        grouped
          | _ : _ <- relations = Just $ ARelation $ foldr1 relationJoin relations
          | otherwise = Nothing

        deep as
          | weak = foldr1 AJoin as -- Don't descend
          | otherwise = group $ foldr (gather True) [] as

    groupFixpoints :: [Annotation] -> Maybe Annotation
    groupFixpoints annotations
      | null fixpoints = Nothing
      | otherwise = Just $ AFix fixpointF fixpointSort fixpointG
      where
        (fixpoints, parts) = gatherFixpoints annotations

        singleFixpoint
          | [_] <- fixpoints = True
          | otherwise = False

        fixpointSort
          | [(s, _)] <- fixpoints = s
          | otherwise = SortTuple $ map (\(s, _) -> s) fixpoints

        fixpointF = ALam fixpointSort RegionSortUnit LifetimeContextAny $ foldr1 AJoin $ map fixpointFBody parts
        fixpointFBody (Right a) = weaken 0 1 0 a
        fixpointFBody (Left (idx, f)) = AApp (weaken 0 1 0 f) (if singleFixpoint then AVar (AnnotationVar 0) else AProject (AVar $ AnnotationVar 0) idx) (RegionVarsTuple []) LifetimeContextAny

        fixpointG
          | [(_, g)] <- fixpoints = g
          | otherwise = ALam fixpointSort RegionSortUnit LifetimeContextAny $ ATuple
            $ zipWith (\(_, g) i -> AApp (weaken 0 1 0 g) (AProject (AVar $ AnnotationVar 0) i) (RegionVarsTuple []) LifetimeContextAny) fixpoints [0..]

    gather :: Bool -> Annotation -> [Annotation] -> [Annotation]
    gather simplified (AJoin a1 a2) = gather simplified a1 . gather simplified a2
    gather False a1 = gather True $ (if weak then weakSimplify else simplify) env a1
    gather True a1 = (a1 :)

    isExtreme (ABottom _) = True
    isExtreme (ATop _) = True
    isExtreme _ = False

    isTop (ATop _) = True
    isTop _ = False

    isForall (AForall _ _) = True
    isForall _ = False

    isLam (ALam _ _ _ _) = True
    isLam _ = False

    isRelation (ARelation _) = True
    isRelation _ = False

    isTuple (ATuple _) = True
    isTuple _ = False

topApplication :: Sort -> RegionSort -> Annotation -> RegionVars -> LifetimeContext -> Sort -> (IsWeakSimplified, Annotation)
topApplication argSort _ arg _ LifetimeContextLocalBottom returnSort
  = topApplication argSort RegionSortUnit arg (RegionVarsTuple []) LifetimeContextAny returnSort

topApplication argSort regionSort arg regions LifetimeContextAny returnSort
  | regionSort /= RegionSortUnit && all (== RegionGlobal) (flattenRegionVars regions)
  = topApplication argSort RegionSortUnit arg (RegionVarsTuple []) LifetimeContextAny returnSort

  | SortRelation <- argSort
  , SortRelation <- returnSort
  = (False, AJoin arg $ topRelation regions)

  | SortUnit <- returnSort
  = (True, ATuple [])

  | SortUnit <- argSort
  , RegionSortUnit <- regionSort
  = (False, ATop returnSort)

  | RegionSortUnit <- regionSort
  = (True, AApp (ATop sortFun) arg (RegionVarsTuple []) LifetimeContextAny)

  | SortRelation <- argSort
  = (False, AApp (ATop sortFun') (AJoin arg $ topRelation regions) (RegionVarsTuple []) LifetimeContextAny)

  | SortUnit <- argSort
  , SortRelation <- returnSort
  = (True, topRelation regions)

  | SortRelation <- returnSort
  = ( False
    , AJoin
        (AApp (ATop sortFun') arg (RegionVarsTuple []) LifetimeContextAny)
        (topRelation regions)
    )

  | otherwise
  = (True, AApp (ATop sortFun) arg regions LifetimeContextAny)

  where
    sortFun = SortFun argSort regionSort LifetimeContextAny returnSort
    sortFun' = SortFun argSort RegionSortUnit LifetimeContextAny returnSort

topRelation :: RegionVars -> Annotation
topRelation regions = arelation $ relationFromConstraints $ map (`Outlives` RegionGlobal) $ flattenRegionVars regions

-- Applies 'f' to the body of the lambda in annotation.
-- If the annotation is not yet a lambda, it will put it in a lambda.
-- Note that as 'f' is applied within the lambda, it is applied to a nested environment
-- and may need to weaken annotation variables.
mapInFunction :: (Annotation -> Annotation) -> Sort -> Annotation -> Annotation
mapInFunction f _ (ALam s rs lc a) = ALam s rs lc $ f a
mapInFunction f s a = ALam s (RegionSortTuple []) LifetimeContextAny $ f $ AApp (weaken 0 1 0 a) (AVar $ AnnotationVar 0) (RegionVarsTuple []) LifetimeContextAny

mapInFunction' :: (Annotation -> Annotation) -> Sort -> RegionSort -> Annotation -> Annotation
mapInFunction' f _ _ (ALam s rs lc a) = ALam s rs lc $ f a
mapInFunction' f s rs a = ALam s rs LifetimeContextAny $ f $ AApp (weaken 0 1 (regionSortSize rs) a) (AVar $ AnnotationVar 0) (regionSortToVars 0 rs) LifetimeContextAny

-- Composes two functions (which do not take region arguments)
-- by appling the first function after the second function.
compose :: Sort -> Annotation -> Annotation -> Annotation
compose s f g = mapInFunction (\a -> AApp (weaken 0 1 0 f) a (RegionVarsTuple []) LifetimeContextAny) s g

-- f (fix g)
afix :: Bool -> DataTypeEnv -> AFix -> Annotation
afix widen env (f, s, g) = simplify env $ snd $ apply env f solution (RegionVarsTuple []) LifetimeContextAny
  where
    g' = simplify env g
    solution = simplify env $ snd $ apply env g' (ATop s) (RegionVarsTuple []) LifetimeContextAny -- TODO

type AFix = (Annotation, Sort, Annotation)
-- Transforms a fixpoint `f (fix g)` to (f . h) (fix (h^-1 . g . h))
-- where h : s' -> s, g : s -> s
transformFixpoint :: AFix -> Sort -> Annotation -> Annotation -> AFix
transformFixpoint (f, _, g) s' h hInv =
  ( compose s' f h
  , s'
  , compose s' hInv $ compose s' g h
  )

afixEscape :: DataTypeEnv -> RegionSort -> [(Int, Sort, Annotation)] -> [([Bool], RegionVar -> RegionVar, Annotation)]
afixEscape env regionSort fs
  = afixEscape' env regionSort fs'
  where
    fs' = zipWith inline [0..] fs
    -- Relies on the laziness of tuples. The third element of the tuple depends on the second element (sort)
    -- of all elements.
    sortTuple = SortTuple $ map (\(_, s, _) -> s) fs'

    inline outerIndex (arity, sort', ALam _ RegionSortUnit LifetimeContextAny g) =
      ( arity
      , sort''
      , ALam (SortFun sortTuple RegionSortUnit LifetimeContextAny sort'') RegionSortUnit LifetimeContextAny g'
      )
      where
        (sort'', g') = inlineFixEscapeTuple outerIndex sort' g

afixEscape' :: DataTypeEnv -> RegionSort -> [(Int, Sort, Annotation)] ->  [([Bool], RegionVar -> RegionVar, Annotation)]
afixEscape' env regionSort fs = -- traceShow ("AFIXESCAPE' ", AFixEscape regionSort fs') $
  projectZero <$> iterate 0 (map firstThird $ escapes' noEscapes $ step $ bottom)
  where
    third (_, _, a) = a
    firstThird (e, _, a) = (e, a)

    noEscapes = map (const $ replicate (regionSortSize regionSort) False) fs
    bottom = map (\(_, s, _) -> ABottom s) fs
    top = map (\(_, s, _) -> ATop s) fs

    fs' = map (\(a, s, g) -> (a, s, simplify env g)) fs

    iterate :: Int -> [([Bool], Annotation)] -> [([Bool], RegionVar -> RegionVar, Annotation)]
    iterate 8 _ -- Give up
      -- Decide on the escapes check, put the remainder in a normal fixpoint
      -- | ALam s rs lc body <- f' -- TODO: We could use f'^n for some n here, as that may give better results in the escapes check
      -- , (doesEscape, substituteRegionVar, body') <- escapes' body
      --   = (doesEscape, substituteRegionVar, AFix (identity sort') sort' $ ALam s rs lc body')
      | otherwise = escapes' noEscapes $ step $ top
    iterate i current
      | {- traceShow ("iterate", i) $ -} map snd current == map third next = next
      | otherwise = iterate (i+1) $ map firstThird next
      where
        next = escapes' (map fst current) $ step $ map snd current

    projectZero :: ([Bool], RegionVar -> RegionVar, Annotation) -> ([Bool], RegionVar -> RegionVar, Annotation)
    projectZero (doesEscape, substitute, a) = (doesEscape, substitute, mapInFunction' (`AProject` 0) SortUnit regionSort a)

    step :: [Annotation] -> [Annotation]
    step as = map (\(_, _, f) -> simplify env $ AApp f a (RegionVarsTuple []) LifetimeContextAny) fs'
      where
        a = ATuple as

    escapes' :: [[Bool]] -> [Annotation] -> [([Bool], RegionVar -> RegionVar, Annotation)]
    escapes' =
      zipWith3 (\(arity, _, _) -> escapes arity regionSort) fs'

untuple :: Int -> Annotation -> [Annotation]
untuple _ (ATuple as) = as
untuple len a = map (AProject a) [0 .. len - 1]

-- Returns:
-- * For each region whether it escapes
-- * Substitution of the additional region arguments
-- * The transformed annotation
escapes :: Int -> RegionSort -> [Bool] -> Annotation -> ([Bool], RegionVar -> RegionVar, Annotation)
escapes arity regionSort forceEscape (AFix (ALam s rs lc a) s' a') =
  let
    (doesEscape, substituteRegionVar, a'') = escapes arity regionSort forceEscape a
  in
    (doesEscape, substituteRegionVar, AFix (ALam s rs lc a'') s' a')
escapes _     regionSort forceEscape a@(ABottom _) = (forceEscape, id, a) -- Both Top and Bottom don't need additional region arguments.
escapes _     regionSort forceEscape a@(ATop _) = (forceEscape, id, a)
escapes arity regionSort forceEscape (ALam sort' regionSort' lifetime (ATuple (a : as))) =
  let
    (doesEscape, substituteRegionVar, a') = skipLambdas arity (reverse $ flattenRegionSort regionSort') 0 a
  in
    (doesEscape, substituteRegionVar, ALam sort' regionSort' lifetime $ ATuple $ a' : as)
  where
    regionSize = regionSortSize regionSort

    skipLambdas :: Int -> [RegionSort] -> Int -> Annotation -> ([Bool], RegionVar -> RegionVar, Annotation)
    skipLambdas 0 _ _ a1 = (replicate regionSize True, id, a1)
    skipLambdas 1 regionScopeList regionScope (ALam s rs lc a1) = (doesEscape, substituteRegionVar, ALam s rs lc a1')
      where
        (doesEscape, substituteRegionVar, a1') = escapesBody regionSort (reverse (flattenRegionSort rs) ++ regionScopeList) (regionScope + regionSortSize rs) forceEscape a1
    skipLambdas n regionScopeList regionScope (AForall q a1) = (doesEscape, substituteRegionVar, AForall q a1')
      where
        (doesEscape, substituteRegionVar, a1') = skipLambdas n regionScopeList regionScope a1
    skipLambdas n regionScopeList regionScope (ALam s rs lc (ATuple [a1, a2])) = (doesEscape, substituteRegionVar, ALam s rs lc (ATuple [a1', a2']))
      where
        a1' = restrict doesEscape (regionScope + regionSortSize rs) a1
        (doesEscape, substituteRegionVar, a2') = skipLambdas (n - 1) (reverse (flattenRegionSort rs) ++ regionScopeList) (regionScope + regionSortSize rs) a2
    skipLambdas _ _ _ _ = error "Helium.CodeGeneration.Iridium.Region.Annotation.escapes: annotation does not match with the function arity"

    restrict :: [Bool] -> Int -> Annotation -> Annotation
    restrict doesEscape regionScope annotation = case annotation of
        AFix f s g -> AFix (go f) s (go g)
        AFixEscape rs fs -> AFixEscape rs $ map (\(a, s, f) -> (a, s, go f)) fs
        AForall q a1 -> AForall q (go a1)
        ALam s rs lc a1 -> ALam s rs lc $ restrict doesEscape (regionScope + regionSortSize rs) a1
        AInstantiate a1 tp -> AInstantiate (go a1) tp
        AApp a1 a2 rs lc -> AApp (go a1) (go a2) (mapRegionVars mapRegion rs) lc
        ATuple as -> ATuple $ go <$> as
        AProject a1 idx -> AProject (go a1) idx
        AVar v -> AVar v
        ARelation rel -> arelation $ relationFilter preserveRegion rel
        ATop s -> ATop s
        ABottom s -> ABottom s
        AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = restrict doesEscape regionScope

        mapRegion :: RegionVar -> RegionVar
        mapRegion r
          | preserveRegion r = RegionBottom
          | otherwise = r

        preserveRegion :: RegionVar -> Bool
        preserveRegion (RegionLocal idx)
          | idx >= regionScope
          , idx < regionScope + regionSize
          , not $ doesEscape !!! (regionSize - (idx - regionScope) - 1) = False
        preserveRegion _ = True

escapes _ regionSort _ a = (map (const True) $ flattenRegionVars $ regionSortToVars 0 regionSort, id, a) -- This cannot be analyzed

escapesBody :: RegionSort -> [RegionSort] -> Int -> [Bool] -> Annotation -> ([Bool], RegionVar -> RegionVar, Annotation)
escapesBody regionSort extraRegionScopeList extraRegionScope forceEscape (ATop (SortTuple [s1, s2])) = escapesBody regionSort extraRegionScopeList extraRegionScope forceEscape (ATuple [ATop s1, ATop s2])
escapesBody regionSort extraRegionScopeList extraRegionScope forceEscape (ATuple
    [ ATop (SortFun SortUnit RegionSortMonomorphic LifetimeContextAny (SortFun SortUnit returnRegionSort LifetimeContextLocalBottom sEffect))
    , aReturn
    ])
  = escapesBody regionSort extraRegionScopeList extraRegionScope forceEscape (ATuple
    [ ALam SortUnit RegionSortMonomorphic LifetimeContextAny (ALam SortUnit returnRegionSort LifetimeContextLocalBottom (ATop sEffect))
    , aReturn
    ])
escapesBody regionSort extraRegionScopeList extraRegionScope forceEscape (ATuple
    [ ALam SortUnit RegionSortMonomorphic LifetimeContextAny (ALam SortUnit returnRegionSort LifetimeContextLocalBottom aEffect)
    , aReturn
    ])
  = ( doesEscape
    , substituteRegionVar 0
    , ATuple
      [ ALam SortUnit RegionSortMonomorphic LifetimeContextAny $ ALam SortUnit returnRegionSort LifetimeContextLocalBottom $ substitute 0 aEffect
      , fromMaybe (error $ "escapesBody: illegal variable.\naReturn:\n" ++ show aReturn ++ "\naReturn':\n" ++ show aReturn' ++ "\nSubstituted:\n" ++ show (substitute 0 aReturn') ++ "\nSubstitution:\n" ++ show substitution) $ strengthen 0 0 (regionSortSize returnRegionSort + 1) $ substitute 0 aReturn'
      ]
    )
  where
    aReturn' = weaken 0 0 (regionSortSize returnRegionSort + 1) aReturn
    extraRegionScope' = extraRegionScope + regionSortSize returnRegionSort + 1

    regionSize = regionSortSize regionSort
    Escapes relation higherOrderVars = analyseEscapeBody False 0 aEffect <> analyseEscapeBody True 0 aReturn'

    (_, substitutionList) = relationCollapse canCollapse canDefault canUnifyWith (map RegionLocal [extraRegionScope' .. extraRegionScope' + regionSize - 1]) relation
    substitution = IntMap.fromList $ map (\(RegionVar idx, r) -> (idx, r)) substitutionList

    canCollapse (RegionLocal idx) = idx >= extraRegionScope' && idx < extraRegionScope' + regionSize && not (forceEscape !! (extraRegionScope' + regionSize - idx - 1))
    canCollapse _ = False

    canDefault (RegionLocal idx) = canCollapse (RegionLocal idx) && idx `IntSet.notMember` higherOrderVars
    canDefault _ = False

    canUnifyWith (RegionLocal idx1) (RegionLocal idx2) = extraRegionScopeList' !! idx1 == extraRegionScopeList' !! idx2
    canUnifyWith _ _ = True

    extraRegionScopeList' = reverse (flattenRegionSort returnRegionSort) ++ [RegionSortMonomorphic] ++ extraRegionScopeList

    doesEscape = map (\var -> substituteRegionVar 0 var == var) $ reverse $ map RegionLocal $ [extraRegionScope' .. extraRegionScope' + regionSize - 1]

    substitute :: Int -> Annotation -> Annotation
    substitute scope annotation = case annotation of
        AFix f s g -> AFix (go f) s (go g)
        AFixEscape rs fs -> AFixEscape rs $ map (\(a, s, f) -> (a, s, go f)) fs
        AForall q a -> AForall q (go a)
        ALam s rs lc a -> ALam s rs lc $ substitute (scope + regionSortSize rs) a
        AInstantiate a tp -> AInstantiate (go a) tp
        AApp a1 a2 rs lc -> AApp (go a1) (go a2) (mapRegionVars (substituteRegionVar scope) rs) lc
        ATuple as -> ATuple $ go <$> as
        AProject a idx -> AProject (go a) idx
        AVar v -> AVar v
        ARelation rel -> arelation $ relationReindex (substituteRegionVar scope) rel
        ATop s -> ATop s
        ABottom s -> ABottom s
        AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = substitute scope

    substituteRegionVar :: Int -> RegionVar -> RegionVar
    substituteRegionVar scope (RegionLocal idx)
      | idx >= scope
      , idx' <- idx - scope
      , canCollapse (RegionLocal idx')
      , Just r <- IntMap.lookup idx' substitution
      -- The variable is substituted with 'r'.
      -- Recursively call 'substituteRegionVar' on 'r', as that variable might be
      -- substituted with another variable.
        = substituteRegionVar scope $ weakenRegionVar 0 scope r
    substituteRegionVar _ r = r
escapesBody rs _ _ _ body = (if isBottom body || isTopApplication body then id else trace "escapesBody: unexpected body annotation") (map (const True) $ flattenRegionVars $ regionSortToVars 0 rs, id, body)

analyseEscapeBody :: Bool -> Int -> Annotation -> Escapes
analyseEscapeBody isReturn firstRegionScope annotation = case annotation of
    AFix f _ g -> go f <> go g
    AFixEscape _ fs -> mconcat $ map (\(_, _, f) -> go f) fs
    AForall _ a1 -> go a1
    ALam _ rs _ a1 -> analyseEscapeBody isReturn (firstRegionScope + regionSortSize rs) a1
    AInstantiate a1 _ -> go a1
    AApp a1 a2 rs lc ->
      let
        r
          | lc == LifetimeContextLocalBottom && not isReturn
            -- In the effect annotation, we may ignore regions used in local-bottom arguments
            = mempty
          | lc == LifetimeContextAny && rs /= RegionVarsTuple [] && isTopApplication a1
            = Escapes (relationFromConstraints $ map ((`Outlives` RegionGlobal) . RegionLocal) $ mapMaybe regionIdx $ flattenRegionVars rs) IntSet.empty
          | otherwise
            = Escapes relationEmpty $ IntSet.fromList $ mapMaybe regionIdx $ flattenRegionVars rs
      in go a1 <> go a2 <> r
    ATuple as -> mconcat $ go <$> as
    AProject a1 _ -> go a1
    AVar _ -> mempty
    ATop _ -> mempty
    ABottom _ -> mempty
    AJoin a1 a2 -> go a1 <> go a2
    ARelation rel ->
      let
        (vars, rel') = relationRestrict firstRegionScope rel
        vars'
          | isReturn = relationVars rel
          | otherwise = []
      in Escapes rel' $ IntSet.fromList $ map regionVarIndex (vars' ++ vars)
  where
    go = analyseEscapeBody isReturn firstRegionScope

    regionIdx :: RegionVar -> Maybe Int
    regionIdx (RegionLocal idx)
      | idx >= firstRegionScope = Just $ idx - firstRegionScope
    regionIdx _ = Nothing

-- Checks if the annotation is an instantiation or application of top
isTopApplication :: Annotation -> Bool
isTopApplication (ATop _) = True
isTopApplication (AApp a _ _ _) = isTopApplication a
isTopApplication (AInstantiate a _) = isTopApplication a
isTopApplication (AJoin a1 a2) = isTopApplication a2 || isTopApplication a1
isTopApplication _ = False

isBottom :: Annotation -> Bool
isBottom (ABottom _) = True
isBottom _ = False

-- Local state in 'escapes'
data Escapes = Escapes !Relation !IntSet deriving Show

instance Semigroup Escapes where
  Escapes relation1 set1 <> Escapes relation2 set2 = Escapes (relationJoin relation1 relation2) (IntSet.union set1 set2)

instance Monoid Escapes where
  mempty = Escapes relationEmpty IntSet.empty

annotationRestrict :: [Bool] -> Annotation -> (Int, Annotation)
annotationRestrict preserve annotation
  | ALam s (RegionSortTuple regionSorts) lifetime a1 <- annotation
    = (newCount, ALam s (RegionSortTuple $ map snd $ filter fst $ zip preserve regionSorts) lifetime $ transform 0 a1)
  | AFix (ALam s RegionSortUnit LifetimeContextAny a1) s' a2 <- annotation
  , (count, a1') <- annotationRestrict preserve a1
    = (count, AFix (ALam s RegionSortUnit LifetimeContextAny a1') s' a2)
  | otherwise = (length preserve, annotation)
  where
    oldCount = length preserve
    newCount = length $ filter id preserve

    mapping :: [Maybe Int]
    (_, mapping) = mapAccumL f 0 $ reverse preserve

    f :: Int -> Bool -> (Int, Maybe Int)
    f idx False = (idx, Nothing)
    f idx True = (idx + 1, Just idx)

    transform :: Int -> Annotation -> Annotation
    transform regionCount a = case a of
      AFix a1 s a2 -> AFix (transform' a1) s (transform' a2)
      AFixEscape rs fs -> AFixEscape rs $ map (\(a, s, f) -> (a, s, transform' f)) fs
      AForall q a1 -> AForall q $ transform' a1
      ALam s regionSort lifetime a1 -> ALam s regionSort lifetime $ transform (regionCount + regionSortSize regionSort) a1
      AInstantiate a1 tp -> AInstantiate (transform' a1) tp
      AApp a1 a2 rs lc -> AApp (transform' a1) (transform' a2) (transformRegionVars rs) lc
      ATuple as -> ATuple $ map transform' as
      AProject a1 idx -> AProject (transform' a1) idx
      AVar (AnnotationVar idx) -> AVar $ AnnotationVar idx
      ARelation rel -> ARelation $ relationReindex transformRegionVar $ relationFilter (isJust . transformRegionVarM) rel
      ATop s -> ATop s
      ABottom s -> ABottom s
      AJoin a1 a2 -> AJoin (transform' a1) (transform' a2)
      where
        transform' = transform regionCount

        transformRegionVar :: RegionVar -> RegionVar
        transformRegionVar r = fromMaybe RegionBottom $ transformRegionVarM r

        transformRegionVarM :: RegionVar -> Maybe RegionVar
        transformRegionVarM (RegionLocal idx)
          | idx >= regionCount && idx < regionCount + oldCount =
            case mapping !!! (idx - regionCount) of
              Nothing -> Nothing
              Just idx' -> Just $ RegionLocal $ idx' + regionCount
        transformRegionVarM r = Just r

        transformRegionVars :: RegionVars -> RegionVars
        transformRegionVars = mapRegionVars transformRegionVar

inlineFixEscapeTuple :: Int -> Sort -> Annotation -> (Sort, Annotation)
inlineFixEscapeTuple outerIndex (SortFun SortUnit regionSort lc (SortTuple sorts)) (ALam _ _ _ (ATuple annotations@(_ : _)))
  | Just dependencies <- traverse (gatherDependencies 0 0) $ annotations
  -- First element must always be manifest, as that is the result of the fixpoint.
  , recursive <- True : snd (mapAccumL (\seen idx -> if isRecursive dependencies seen idx idx then (idx : seen, True) else (seen, False)) [0] $ zipWith const [1..] $ tail annotations)
  -- We only preserve the elements which are recursive.
  -- Here we construct a mapping from the original indices to the indices of the resulting array.
  , mapping <- scanl (+) 0 $ map (\r -> if r then 1 else 0) recursive
  = ( SortFun SortUnit regionSort lc $ SortTuple
        $ map snd $ filter fst $ zip recursive sorts
    , ALam SortUnit regionSort lc $ ATuple
        $ map snd $ filter fst $ zip recursive $ map (inline recursive mapping 0 0) annotations
    )
  where
    gatherDependencies :: Int -> Int -> Annotation -> Maybe [Int]
    gatherDependencies lambdaCount regionCount a = case a of
      AProject (AApp (AProject (AVar (AnnotationVar idx)) outerIndex') (ATuple []) regions LifetimeContextAny) i
        | outerIndex == outerIndex'
        , idx == lambdaCount + 1
        , regions == regionSortToVars regionCount regionSort -> Just [i]
        | outerIndex /= outerIndex'
        , idx == lambdaCount + 1
        , i == 0
        , regions == regionSortToVars regionCount regionSort -> Just []
        | idx == lambdaCount + 1 -> Nothing
      AFix a1 _ a2 -> go a1 `combine` go a2
      AFixEscape _ fs -> foldl' combine (Just []) $ map (\(_, _, a) -> go a) fs
      AForall _ a1 -> go a1
      ALam _ rs' _ a1 -> gatherDependencies (lambdaCount + 1) (regionCount + regionSortSize rs') a1
      AInstantiate a1 _ -> go a1
      AApp a1 a2 _ _ -> go a1 `combine` go a2
      ATuple as -> foldl' combine (Just []) $ map go as
      AProject a1 _ -> go a1
      AJoin a1 a2 -> go a1 `combine` go a2
      AVar (AnnotationVar idx)
        | idx == lambdaCount + 1 -> Nothing
      _ -> Just []
      where
        go = gatherDependencies lambdaCount regionCount

        combine (Just xs) (Just []) = Just xs
        combine (Just xs) (Just ys) = Just $ xs ++ ys
        combine _ _ = Nothing

    inline :: [Bool] -> [Int] -> Int -> Int -> Annotation -> Annotation
    inline recursive mapping lambdaCount regionCount a = case a of
      AProject (AApp (AProject (AVar (AnnotationVar idx)) outerIndex') (ATuple []) regions LifetimeContextAny) i
        | outerIndex == outerIndex'
        , idx == lambdaCount + 1
        , regions == regionSortToVars regionCount regionSort ->
          if recursive !! i then
            AProject (AApp (AProject (AVar (AnnotationVar idx)) outerIndex) (ATuple []) regions LifetimeContextAny) (mapping !! i)
          else
            go $ weaken 0 lambdaCount regionCount $ annotations !! i

      AFix a1 s a2 -> AFix (go a1) s (go a2)
      AFixEscape rs fs -> AFixEscape rs $ map (\(a, r, f) -> (a, r, go f)) fs
      AForall q a1 -> AForall q $ go a1
      ALam s rs lc a1 -> ALam s rs lc $ inline recursive mapping (lambdaCount + 1) (regionCount + regionSortSize rs) a1
      AInstantiate a1 tp -> AInstantiate (go a1) tp
      AApp a1 a2 rs lc -> AApp (go a1) (go a2) rs lc
      ATuple as -> ATuple $ map go as
      AProject a1 idx -> AProject (go a1) idx
      AVar var -> AVar var
      ARelation r -> ARelation r
      ATop s -> ATop s
      ABottom s -> ABottom s
      AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = inline recursive mapping lambdaCount regionCount

    isRecursive :: [[Int]] -> [Int] -> Int -> Int -> Bool
    isRecursive dependencies seen start idx
      | idx `elem` seen = False
      | otherwise = any (\idx' -> start == idx' || isRecursive dependencies (idx : seen) start idx') (dependencies !!! idx)

inlineFixEscapeTuple _ s a = (s, a) -- Cannot be simplified
