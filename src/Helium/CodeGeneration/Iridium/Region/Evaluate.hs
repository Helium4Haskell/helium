module Helium.CodeGeneration.Iridium.Region.Evaluate
  ( simplify, weakSimplify, afixEscape --, widen
  , strengthen, weaken
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

simplify :: DataTypeEnv -> Annotation -> Annotation
-- 'join' and 'afix' reduce a value fully, no need to recurse on the sub-annotations
simplify env annotation@AJoin{} = join True env annotation
simplify env (AFix a1 s a2) = afix False env (a1, s, a2)
simplify env annotation = case weakSimplifyStep env annotation of
  (True , annotation') -> nested annotation'
  (False, annotation') -> simplify env annotation'
  where
    nested (ALam argSort regionSort lifetime body)
      | ABottom s <- body' = ABottom (SortFun argSort regionSort lifetime s)
      | AApp f (AVar (AnnotationVar 0)) regions lifetime' <- body'
      , lifetime == lifetime'
      , regions == regionSortToVars 0 regionSort
      , Just f' <- strengthen 0 1 (regionSortSize regionSort) f = f' -- eta reduction
      | otherwise = ALam argSort regionSort lifetime body'
      where
        body' = simplify env body
    nested (AForall q body)
      | ABottom s <- body' = ABottom (SortForall q s)
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
  ATop _ -> (True, annotation)
  ABottom _ -> (True, annotation)
  ARelation{} -> (True, annotation)
  ATuple{} -> (True, annotation)
  AVar{} -> (True, annotation)

  AJoin{} -> (True, join True env annotation)

  AFix a1 s a2 -> (True, afix False env (a1, s, a2))
  AFixEscape arity s rs a -> (False, snd $ afixEscape env arity s rs a)

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
      AFixEscape arity s rs a1 -> AFixEscape arity s rs (transform' a1)
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
      AFixEscape arity s rs a1 -> AFixEscape arity s rs <$> transform' a1
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
    instantiate' _ (ATop s) = (False, ATop $ sortInstantiate dataTypeEnv s tp)
    instantiate' _ (ABottom s) = (True, ABottom $ sortInstantiate dataTypeEnv s tp)
    instantiate' _ (AForall _ a) = (False, transform 0 emptyEnv 0 a)
    instantiate' _ (AFix a1 s a2) = (False, AFix (mapInFunction (transform 0 emptyEnv 0) s a1) s a2)
    instantiate' False a = uncurry instantiate' $ weakSimplifyStep dataTypeEnv a
    instantiate' True a = (True, AInstantiate a tp)

    -- Note that the values (region vars) in the environment nor the keys are RegionGlobal or RegionBottom,
    -- and that the RegionVars are Debruijn levels instead of indices
    transform :: Int -> Env RegionVars -> Int -> Annotation -> Annotation
    transform forallCount env newEnvSize a = case a of
      AFix a1 s a2 -> AFix (transform' a1) (transformSort s) $ transform' a2
      AFixEscape arity s rs a1 -> AFixEscape arity (transformSort s) (transformRegionSort rs) $ transform' a1
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
        transformType tp1 = typeSubstitute forallCount tp1 $ typeWeaken forallCount tp
        transformSort = sortSubstitute dataTypeEnv forallCount tp
        transformRegionSort = regionSortSubstitute dataTypeEnv forallCount tp

        transformRegions :: RegionVars -> RegionVars
        transformRegions = mapRegionVars (\(RegionVar level) -> RegionVar $ newEnvSize - 1 - level) . bindRegionVars (\(RegionVar idx) -> envFind idx env)

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
  | otherwise = apply' 0 False annotation
  where
    apply' :: Int -> IsWeakSimplified -> Annotation -> (IsWeakSimplified, Annotation)
    apply' lambdaCount simplified (AJoin a1 a2) = (False, AJoin (snd $ apply' lambdaCount simplified a1) (snd $ apply' lambdaCount simplified a2))
    apply' _ _ (ABottom s) = case s of
      SortFun _ _ _ s' -> (True, ABottom s')
      _ -> error $ "Helium.CodeGeneration.Iridium.Region.Annotation.apply: Bottom has wrong sort: " ++ showSort [] s ""
    apply' lambdaCount _ (ALam _ rs _ body) = (False, substitute (regionVarMapping rs argumentRegion []) lambdaCount 0 body)
    apply' lambdaCount simplified (AFix a1 s a2) = (False, AFix (mapInFunction (snd . apply' (lambdaCount + 1) simplified) s a1) s a2) -- Start with lambdaCount=1, as mapInFunction also creates a lambda. This lambda does not have region arguments.
    apply' lambdaCount False annotation' = uncurry (apply' lambdaCount) $ weakSimplifyStep env annotation'
    apply' lambdaCount True  annotation' = (True, AApp annotation' argument argumentRegion lc)

    -- TODO: Rewrite with zipFlattenRegionVars?
    regionVarMapping :: RegionSort -> RegionVars -> [RegionVar] -> [RegionVar]
    regionVarMapping (RegionSortForall _ rs)    vars                         accum = regionVarMapping rs vars accum
    regionVarMapping rs                         (RegionVarsSingle var)       accum = map (const var) (flattenRegionVars $ regionSortToVars 0 rs) ++ accum
    regionVarMapping RegionSortUnit             (RegionVarsTuple [])         accum = accum
    regionVarMapping (RegionSortTuple (rs:rss)) (RegionVarsTuple (var:vars)) accum = regionVarMapping rs var $ regionVarMapping (RegionSortTuple rss) (RegionVarsTuple vars) accum
    regionVarMapping _ _ _ = error "Helium.CodeGeneration.Iridium.Region.Evaluate.apply: region sort mismatch"

    argument' = simplify env argument

    substitute :: [RegionVar] -> Int -> Int -> Annotation -> Annotation
    substitute regions lambdaCount regionArgCount annotation = case annotation of
      AFix a1 s a2 -> AFix (go a1) s (go a2)
      AFixEscape arity s rs a1 -> AFixEscape arity s rs $ go a1

      AForall q a -> AForall q $ go a
      ALam sort regionSort lifetime a -> ALam sort regionSort lifetime $ substitute regions (lambdaCount + 1) (regionArgCount + regionSortSize regionSort) a

      AInstantiate a tp -> AInstantiate (go a) tp
      AApp a1 a2 regions' lc' -> AApp (go a1) (go a2) regions' lc'

      ATuple as -> ATuple $ map go as
      AProject a idx -> AProject (go a) idx

      AVar (AnnotationVar idx)
        | idx <  lambdaCount -> AVar $ AnnotationVar idx
        | idx == lambdaCount -> weaken 0 lambdaCount regionArgCount argument'
        | otherwise          -> AVar $ AnnotationVar $ idx - 1

      ARelation relation -> arelation $ relationReindex substituteRegion relation

      ABottom s -> ABottom s
      ATop s -> ATop s
      AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = substitute regions lambdaCount regionArgCount
        argumentRegionSize = length regions
        substituteRegion (RegionVar idx)
          | idx < regionArgCount = RegionVar idx
          | idx < regionArgCount + argumentRegionSize = regions !! (regionArgCount + argumentRegionSize - idx - 1)
          | otherwise = RegionVar $ idx - regionArgCount

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
      Nothing -> error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Bottom: Index out of bounds"
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
    projectSort _ = error "Helium.CodeGeneration.Iridium.Region.Annotation.project: Top: Illegal sort"

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
          $ [ a | AForall _ a <- parts ]
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

-- Applies 'f' to the body of the lambda in annotation.
-- If the annotation is not yet a lambda, it will put it in a lambda.
-- Note that as 'f' is applied within the lambda, it is applied to a nested environment
-- and may need to weaken annotation variables.
mapInFunction :: (Annotation -> Annotation) -> Sort -> Annotation -> Annotation
mapInFunction f _ (ALam s rs lc a) = ALam s rs lc $ f a
mapInFunction f s a = ALam s (RegionSortTuple []) LifetimeContextAny $ f $ AApp (weaken 0 1 0 a) (AVar $ AnnotationVar 0) (RegionVarsTuple []) LifetimeContextAny

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

afixEscape :: DataTypeEnv -> Int -> Sort -> RegionSort -> Annotation -> ([Bool], Annotation)
afixEscape env arity sort' regionSort f = iterate 0 $ snd $ escapes' $ step $ ABottom sort'
  where
    f' = simplify env f

    iterate :: Int -> Annotation -> ([Bool], Annotation)
    iterate 16 _ -- Give up
      -- Decide on the escapes check, put the remainder in a normal fixpoint
      | ALam s rs lc body <- f' -- TODO: We could use f'^n for some n here, as that may give better results in the escapes check
      , (doesEscape, body') <- escapes' body
        = (doesEscape, AFix (identity sort') sort' $ ALam s rs lc body')
      | otherwise = escapes' $ step (ATop sort')
    iterate i current
      | current == next = (doesEscape, next)
      | otherwise = iterate (i+1) next
      where
        (doesEscape, next) = escapes' $ step current

    step a = simplify env $ AApp f' a (RegionVarsTuple []) LifetimeContextAny
    escapes' = escapes arity regionSort

escapes :: Int -> RegionSort -> Annotation -> ([Bool], Annotation) -- For each region whether it escapes, and the transformed annotation
escapes arity regionSort (AFix (ALam _ _ _ a) _ _) = escapes arity regionSort a
escapes _     regionSort a@(ABottom _) = (map (const False) $ flattenRegionVars $ regionSortToVars 0 regionSort, a) -- Both Top and Bottom don't need additional region arguments.
escapes _     regionSort a@(ATop _) = (map (const False) $ flattenRegionVars $ regionSortToVars 0 regionSort, a)
escapes arity regionSort  (ALam _ _ _ a) = skipLambdas arity 0 a
  where
    regionSize = regionSortSize regionSort

    skipLambdas :: Int -> Int -> Annotation -> ([Bool], Annotation)
    skipLambdas 0 regionScope a1 = escapesBody regionSort regionScope a1
    skipLambdas n regionScope (AForall q a1) = AForall q <$> skipLambdas n regionScope a1
    skipLambdas n regionScope (ALam s rs lc (ATuple [a1, a2])) = (doesEscape, ALam s rs lc (ATuple [a1', a2']))
      where
        a1' = restrict doesEscape regionScope a1
        (doesEscape, a2') = skipLambdas (n - 1) (regionScope + regionSortSize rs) a2
    skipLambdas _ _ _ = error "Helium.CodeGeneration.Iridium.Region.Annotation.escapes: annotation does not match with the function arity"

    restrict :: [Bool] -> Int -> Annotation -> Annotation
    restrict doesEscape regionScope annotation = case annotation of
        AFix f s g -> AFix (go f) s (go g)
        AFixEscape arity s rs a1 -> AFixEscape arity s rs $ go a1
        AForall q a1 -> AForall q (go a1)
        ALam s rs lc a1 -> ALam s rs lc $ restrict doesEscape (regionScope + regionSortSize rs) a1
        AInstantiate a1 tp -> AInstantiate (go a1) tp
        AApp a1 a2 rs lc
          | not $ all preserveRegion $ flattenRegionVars rs -> error "Helium.CodeGeneration.Iridium.Region.Annotation.escapes: illegal application in annotation"
          | otherwise -> AApp (go a1) (go a2) rs lc
        ATuple as -> ATuple $ go <$> as
        AProject a1 idx -> AProject (go a1) idx
        AVar v -> AVar v
        ARelation rel -> arelation $ relationFilter preserveRegion rel
        ATop s -> ATop s
        ABottom s -> ABottom s
        AJoin a1 a2 -> AJoin (go a1) (go a2)
      where
        go = restrict doesEscape regionScope

        preserveRegion :: RegionVar -> Bool
        preserveRegion (RegionLocal idx)
          | idx >= regionScope
          , idx < regionScope + regionSize
          , not $ doesEscape !!! (regionSize - (idx - regionScope) + 1) = False
        preserveRegion _ = True

escapes _ regionSort a = (map (const True) $ flattenRegionVars $ regionSortToVars 0 regionSort, a) -- This cannot be analyzed

escapesBody :: RegionSort -> Int -> Annotation -> ([Bool], Annotation)
escapesBody regionSort extraRegionScope body = (doesEscape, substitute 0 body)
  where
    regionSize = regionSortSize regionSort
    Escapes relation higherOrderVars = analyseEscapeBody 0 body

    (_, substitutionList) = relationCollapse canCollapse (filter canCollapse $ map RegionLocal [extraRegionScope .. extraRegionScope + regionSize - 1]) relation
    substitution = IntMap.fromList $ map (\(RegionVar idx, r) -> (idx, r)) substitutionList

    canCollapse (RegionLocal idx) = idx >= extraRegionScope && idx < extraRegionScope + regionSize && idx `IntSet.notMember` higherOrderVars
    canCollapse _ = False

    doesEscape = map (\var -> substituteRegionVar 0 var == var) $ reverse $ map RegionLocal $ [extraRegionScope .. extraRegionScope + regionSize - 1]

    substitute :: Int -> Annotation -> Annotation
    substitute scope annotation = case annotation of
        AFix f s g -> AFix (go f) s (go g)
        AFixEscape arity s rs a1 -> AFixEscape arity s rs $ go a1
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

analyseEscapeBody :: Int -> Annotation -> Escapes
analyseEscapeBody firstRegionScope annotation = case annotation of
    AFix f _ g -> go f <> go g
    AFixEscape _ _ _ a1 -> go a1
    AForall _ a1 -> go a1
    ALam _ rs _ a1 -> analyseEscapeBody (firstRegionScope + regionSortSize rs) a1
    AInstantiate a1 _ -> go a1
    AApp a1 a2 rs lc ->
      let
        r = if lc == LifetimeContextAny && rs /= RegionVarsTuple [] && isTopApplication a1 then
              Escapes (relationFromConstraints $ map ((`Outlives` RegionGlobal) . RegionLocal) $ mapMaybe regionIdx $ flattenRegionVars rs) IntSet.empty
            else
              Escapes relationEmpty $ IntSet.fromList $ mapMaybe regionIdx $ flattenRegionVars rs
      in go a1 <> go a2 <> r
    ATuple as -> mconcat $ go <$> as
    AProject a1 _ -> go a1
    AVar _ -> mempty
    ATop _ -> mempty
    ABottom _ -> mempty
    AJoin a1 a2 -> go a1 <> go a2
    ARelation rel ->
      let (vars, rel') = relationRestrict firstRegionScope rel
      in Escapes rel' $ IntSet.fromList $ map regionVarIndex vars
  where
    go = analyseEscapeBody firstRegionScope

    regionIdx :: RegionVar -> Maybe Int
    regionIdx (RegionLocal idx)
      | idx >= firstRegionScope = Just $ idx - firstRegionScope
    regionIdx _ = Nothing

-- Checks if the annotation is an instantiation or application of top
isTopApplication :: Annotation -> Bool
isTopApplication (ATop _) = True
isTopApplication (AApp a _ _ _) = isTopApplication a
isTopApplication (AInstantiate a _) = isTopApplication a
isTopApplication _ = False

-- Local state in 'escapes'
data Escapes = Escapes !Relation !IntSet

instance Semigroup Escapes where
  Escapes relation1 set1 <> Escapes relation2 set2 = Escapes (relationJoin relation1 relation2) (IntSet.union set1 set2)

instance Monoid Escapes where
  mempty = Escapes relationEmpty IntSet.empty
