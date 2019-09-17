module Helium.CodeGeneration.Iridium.Region.AnnotationNormalize (annotationNormalize, annotationArgumentNormalize, annotationIncrementScope, annotationArgumentRemoveUnusedRegionArguments, argumentToAnnotation, annotationRemoveUnusedFixpoints, annotationArgumentCheckSort, sortCompare) where

import Data.List
import Data.Maybe
import Data.Either
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Control.Applicative.Alternative

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Utils

annotationNormalize :: EffectEnvironment -> SortEnv -> Argument Sort -> Annotation -> Argument Annotation
annotationNormalize env sortEnv sort a = snd <$> annotationNormalize' env sortEnv sort a

type ArgumentAnnotations = Argument (Maybe (Sort, [Annotation]))

-- A modified bind for ArgumentAnnotations
infixl 1 >>~
(>>~) :: ArgumentAnnotations -> (Sort -> Annotation -> ArgumentAnnotations) -> ArgumentAnnotations
arg >>~ f = arg >>= g
  where
    g :: Maybe (Sort, [Annotation]) -> ArgumentAnnotations
    g Nothing = ArgumentValue Nothing
    g (Just (s, as)) = joinArgumentAnnotationsList $ f s <$> as

bindWithSort :: (Argument Sort -> Annotation -> Argument a) -> Argument Sort -> Argument Annotation -> Argument a
bindWithSort f (ArgumentList sorts) (ArgumentList as) = ArgumentList $ zipWith (bindWithSort f) sorts as
bindWithSort f sorts (ArgumentValue a) = f sorts a

argumentAnnotationMap :: (Sort -> Sort) -> (Sort -> Annotation -> Annotation) -> ArgumentAnnotations -> ArgumentAnnotations
argumentAnnotationMap mapSort mapAnnotation = fmap (fmap f)
  where
    f :: (Sort, [Annotation]) -> (Sort, [Annotation])
    f (s, as) = (mapSort s, mapAnnotation s <$> as)

joinArgumentAnnotations :: ArgumentAnnotations -> ArgumentAnnotations -> ArgumentAnnotations
joinArgumentAnnotations (ArgumentValue Nothing) a = a
joinArgumentAnnotations a (ArgumentValue Nothing) = a
joinArgumentAnnotations (ArgumentValue (Just (s, as1))) (ArgumentValue (Just (_, as2)))
  = ArgumentValue $ Just (s, as1 ++ as2)
joinArgumentAnnotations (ArgumentList args1) (ArgumentList args2)
  = ArgumentList $ zipWith joinArgumentAnnotations args1 args2

joinArgumentAnnotationsList :: [ArgumentAnnotations] -> ArgumentAnnotations
joinArgumentAnnotationsList [] = ArgumentValue Nothing
joinArgumentAnnotationsList as = foldr1 joinArgumentAnnotations as

annotationNormalize' :: EffectEnvironment -> SortEnv -> Argument Sort -> Annotation -> Argument (Sort, Annotation)
annotationNormalize' _ _ (ArgumentList []) _ = ArgumentList []
annotationNormalize' env sortEnv sort a
  | sortCompare sort $ annotationCheckSort' env sortEnv [] a =
    let arg = addBottoms sort $ annotationNormalize'' env sortEnv a
    in
      if all (\(s, a) -> sortCompare (ArgumentValue s) $ annotationCheckSort' env sortEnv [] a) $ argumentFlatten arg
        then arg else error $ "sort is incorrect (2)" ++ show arg
  | otherwise = error "annotationNormalize': Sort is incorrect"

addBottoms :: Argument Sort -> ArgumentAnnotations -> Argument (Sort, Annotation)
addBottoms sorts (ArgumentValue Nothing) = (\s -> (s, ABottom)) <$> sorts
addBottoms (ArgumentValue s) (ArgumentValue (Just (_, as))) = ArgumentValue (s, annotationJoin as)
addBottoms (ArgumentList sorts) (ArgumentList annotations) =
  ArgumentList $ zipWith addBottoms sorts annotations
addBottoms sorts args = error $ "annotationNormalize'.addBottoms: Illegal arguments:\n" ++ show sorts ++ "\n" ++ show args

annotationJoin :: [Annotation] -> Annotation
annotationJoin [] = ABottom
annotationJoin [a] = a
annotationJoin as = case annotationGroup as of
  [] -> ABottom
  as' -> foldr1 AJoin as'

annotationJoinUnsorted :: [Annotation] -> Annotation
annotationJoinUnsorted [] = ABottom
annotationJoinUnsorted as = foldr1 AJoin as

annotationGroup :: [Annotation] -> [Annotation]
annotationGroup as =
  nubSort [a | a@AFix{} <- as]
  ++ foralls
  ++ lambdas
  ++ nubSort [a | a@AApp{} <- as]
  ++ nubSort [a | a@AInstantiate{} <- as]
  ++ nubSort [a | a@(AVar _) <- as]
  ++ relation
  where
    nubSort = map head . group . sort
    foralls = case [a | AForall a <- as] of
      [] -> []
      as -> [AForall $ annotationJoin as]
    lambdas = case [(argA, argR, dir, a) | ALam argA argR dir a <- as] of
      [] -> []
      as@((argA, argR, dir, _) : _) -> [ALam argA argR dir $ annotationJoin $ map (\(_,_,_,a) -> a) as]
    relation = case [constraints | ARelation constraints <- as] of
      [] -> []
      [constraints] -> [ARelation constraints]
      list -> [ARelation $ relationToConstraints $ foldr1 relationUnion $ map relationFromTransitiveConstraints list]

annotationNormalize'' :: EffectEnvironment -> SortEnv -> Annotation -> ArgumentAnnotations
annotationNormalize'' env sortEnv a
  | isAppLike =
    annotationNormalize'' env sortEnv a'
    >>~ (\s'' a'' -> annotationApply env sortEnv True s'' a'' args)
    >>~ (\s'' a'' -> ArgumentValue $ Just (s'', [annotationSaturateHead s'' a'']))
  where
    sort = annotationCheckSort' env sortEnv [] a
    (a', args) = gatherApplications a []
    isAppLike = case a of
      AApp _ _ _ _ -> True
      AInstantiate _ _ -> True
      _ -> False
annotationNormalize'' env sortEnv (AFix fixRegions s a) = f <$> annotationIterate env sortEnv fixRegions s a []
  where
    f (higherOrder, s', a') = Just (s', [a'])
annotationNormalize'' env sortEnv (AForall a) = argumentAnnotationMap SortForall (const AForall) $ annotationNormalize'' env sortEnv' a
  where
    sortEnv' = sortEnvIncrement sortEnv
annotationNormalize'' env sortEnv (ATuple as) = ArgumentList $ map (annotationNormalize'' env sortEnv) as
annotationNormalize'' env sortEnv (AProject a idx) = case annotationNormalize'' env sortEnv a of
  ArgumentList as -> as !! idx
  ArgumentValue Nothing -> ArgumentValue Nothing
  ArgumentValue a' -> error $ "annotationNormalize: Expected argument list, got " ++ show a'
annotationNormalize'' env sortEnv (ALam argA argR dir a) = argumentAnnotationMap (SortFun argA argR dir) (const $ ALam argA argR dir) $ annotationNormalize'' env sortEnv' a
  where
    sortEnv' = argumentFlatten argA : sortEnv
annotationNormalize'' env sortEnv ABottom = ArgumentValue Nothing
annotationNormalize'' env sortEnv (AJoin a1 a2) =
  joinArgumentAnnotations (annotationNormalize'' env sortEnv a1) (annotationNormalize'' env sortEnv a2)
annotationNormalize'' env sortEnv (AVar var) = ArgumentValue $ Just (sortEnvLookup sortEnv var, [AVar var])
annotationNormalize'' env sortEnv (ARelation cs) = ArgumentValue $ Just (SortRelation, [ARelation cs])

annotationArgumentNormalize :: EffectEnvironment -> SortEnv -> Argument Sort -> Argument Annotation -> Argument (Sort, Annotation)
annotationArgumentNormalize env sortEnv sort (ArgumentValue annotation)
  | not $ argumentShapeEqual sort annotation' = error $ "AAN: Shape mismatch:\n" ++ show annotation ++ "\n" ++ show annotation' ++ "\n" ++ show sort
  | otherwise = zipArgument (\s a -> (s, a)) sort annotation'
  where
    annotation' = annotationNormalize env sortEnv sort annotation
annotationArgumentNormalize env sortEnv (ArgumentList sorts) (ArgumentList annotations)
  = ArgumentList $ zipWith (annotationArgumentNormalize env sortEnv) sorts annotations

annotationIncrementScope :: Int -> Int -> Annotation -> Annotation
annotationIncrementScope incLambda incForall = annotationIncrementScope' incLambda incForall 1 0

annotationIncrementScope' :: Int -> Int -> Int -> Int -> Annotation -> Annotation
annotationIncrementScope' 0 0 = \_ _ a -> a
annotationIncrementScope' incLambda incForall = increment
  where
    increment :: Int -> Int -> Annotation -> Annotation
    increment minLambda minForall (AFix fixRegions s a) = AFix fixRegions (sortIncreaseScope incForall minForall <$> s) (increment minLambda minForall <$> a)
    increment minLambda minForall (AForall a) = AForall $ increment minLambda (minForall + 1) a
    increment minLambda minForall (ATuple as) = ATuple $ map (increment minLambda minForall) as
    increment minLambda minForall (AProject a idx) = AProject (increment minLambda minForall a) idx
    increment minLambda minForall (ALam annotations regions dir a) = ALam (sortIncreaseScope incForall minForall <$> annotations) (regionIncreaseScope incForall minForall <$> regions) dir $ increment (minLambda + 1) minForall a
    increment minLambda minForall (AApp a1 annotations regions dir) = AApp
      (increment minLambda minForall a1)
      (fmap (increment minLambda minForall) annotations)
      (fmap (variableIncrementLambdaBound minLambda incLambda) regions)
      dir
    increment minLambda minForall (AInstantiate a tp) = AInstantiate (increment minLambda minForall a) (tpIncreaseScope incForall minForall tp)
    increment minLambda minForall (AVar avar) = AVar $ variableIncrementLambdaBound minLambda incLambda avar
    increment minLambda minForall (ARelation constraints) =
      ARelation $ map (\(Outlives r1 r2) -> Outlives (variableIncrementLambdaBound minLambda incLambda r1) (variableIncrementLambdaBound minLambda incLambda r2)) constraints
    increment minLambda minForall ABottom = ABottom
    increment minLambda minForall (AJoin a1 a2) = AJoin (increment minLambda minForall a1) (increment minLambda minForall a2)

annotationApply :: EffectEnvironment -> SortEnv -> Bool -> Sort -> Annotation -> [ApplicationOrInstantiation] -> ArgumentAnnotations
annotationApply env sortEnv _ _ ABottom _ = ArgumentValue Nothing
annotationApply env sortEnv False _ a [] -- All arguments consumed, but target is not yet normalized
  = annotationNormalize'' env sortEnv a
annotationApply env sortEnv True s a [] = ArgumentValue $ Just (s, [a]) -- All arguments consumed, target is normalized
annotationApply env sortEnv _ s (AJoin a1 a2) args -- Join, apply both branches and join the results
  = joinArgumentAnnotations (annotationApply env sortEnv False s a1 args) (annotationApply env sortEnv False s a2 args)
annotationApply env sortEnv False s (AFix fixRegions sort body) args
  = annotationIterate env sortEnv fixRegions sort body args >>= f
  where
    f (_, s', a') = annotationApply env sortEnv True s' a' args
annotationApply env sortEnv _ (SortForall s) (AForall a) (AOIInstantiation tp : args)
  = annotationInstantiate env sortEnv (TypeInstantiation 0 tp) s a >>= (\(s', a') -> annotationApply env sortEnv False s' a' args)
annotationApply env sortEnv _ s1 a1@ALam{} args@(AOIApplication{} : _)
  | not $ sortCompare (ArgumentValue s1) $ annotationCheckSort env sortEnv [] a1 = error "annotationApplyLambda: input sort error"
  | not $ sortCompare (ArgumentValue s1) $ annotationCheckSort env sortEnv [] a1' = error "annotationApplyLambda: input sort error"
  | otherwise = case annotationApplyLambda env sortEnv s1 a1' args [] [] of
  Nothing -> ArgumentValue Nothing
  Just (s2, a2, args')
    | not $ sortCompare (ArgumentValue s2) $ annotationCheckSort env sortEnv [] a2 -> error "annotationApplyLambda: output sort error"
    | otherwise -> annotationApply env sortEnv False s2 a2 args'
  where
    ArgumentValue a1' = annotationNormalize env sortEnv (ArgumentValue s1) a1
annotationApply env sortEnv False s a args = annotationNormalize'' env sortEnv a >>~ (\s' a' -> annotationApply env sortEnv True s' a' args)
annotationApply env sortEnv True s a args = (\(s', a') -> Just (s', [a'])) <$> (annotationAddApplications' env sortEnv s a args)

annotationAddApplications' :: EffectEnvironment -> SortEnv -> Sort -> Annotation -> [ApplicationOrInstantiation] -> Argument (Sort, Annotation)
annotationAddApplications' effectEnv sortEnv (SortForall sort) a (AOIInstantiation tp : args) =
  annotationToArgument (instantiateType effectEnv tp sort) (AInstantiate a tp) >>= (\(s, a') -> annotationAddApplications' effectEnv sortEnv s a' args)
annotationAddApplications' effectEnv sortEnv (SortFun sortA _ _ sort) a (AOIApplication argA argR dir : args) = annotationAddApplications' effectEnv sortEnv sort (AApp a argA' argR dir) args
  where
    argA' = snd <$> annotationArgumentNormalize effectEnv sortEnv sortA argA
annotationAddApplications' effectEnv sortEnv sort a [] = ArgumentValue (sort, a)
annotationAddApplications' _ sortEnv sort a args = error $ "annotationAddApplications: Illegal arguments: " ++ show (sort, a, args)
{-
f a b c

f = \x -> \y -> \z -> g (z = 1, y = 2, x = 3)

Gather: 
a : b : c : []
-}

-- A single region argument may instantiate multiple variables in a lambda. This can happen when a monomorphic region variable
-- is used to instantiate a polymorphic argument. When the annotation containing the polymorphic argument is instantiated with some type,
-- the polymorphic argument may be replaced with a tree of multiple arguments.
-- This only occurs with additional region arguments, which are added to functions for their internal and escaping regions which
-- do not origin from their argument types or return type. We thus only do this for region arguments, not for annotation arguments.
annotationArgumentMapping :: Argument SortArgumentRegion -> Argument RegionVar -> [RegionVar]
annotationArgumentMapping sortArg (ArgumentValue b) = b <$ argumentFlatten sortArg
annotationArgumentMapping (ArgumentList as) (ArgumentList bs) = concat $ zipWith annotationArgumentMapping as bs

{-
tEnv :: EffectEnvironment
tEnv = undefined

tSortEnv :: SortEnv
tSortEnv = [[SortRelation, SortRelation, SortRelation]]

tSort :: Sort
tSort = (SortFun (ArgumentValue SortRelation) argumentEmpty RegionDirectionAny $ SortFun (ArgumentValue SortRelation) argumentEmpty RegionDirectionAny $ SortRelation)

tA :: Annotation
tA = ALam (ArgumentValue SortRelation) argumentEmpty RegionDirectionAny $ ALam (ArgumentValue SortRelation) argumentEmpty RegionDirectionAny $ AVar (variableFromIndices 1 0)

test = annotationApplyLambda tEnv tSortEnv tSort tA [AOIApplication (ArgumentValue $ AVar $ variableFromIndices 1 1) argumentEmpty RegionDirectionAny, AOIApplication (ArgumentValue $ AVar $ variableFromIndices 1 2) argumentEmpty RegionDirectionAny] [] []
-}

annotationApplyLambda :: EffectEnvironment -> SortEnv -> Sort -> Annotation -> [ApplicationOrInstantiation] -> [[Annotation]] -> [[RegionVar]] -> Maybe (Sort, Annotation, [ApplicationOrInstantiation])
annotationApplyLambda _ _ _ ABottom _ _ _ = Nothing
annotationApplyLambda env sortEnv (SortFun sortAnnotation' _ _ s) (ALam sortAnnotation sortRegion _ a) (AOIApplication argA argR dir : args) aSubst rSubst
  | sortAnnotation' /= sortAnnotation = error $ "Sort mismatch: " ++ show sortAnnotation' ++ " & " ++ show sortAnnotation
  | not $ argumentShapeEqual sortAnnotation' argA' = error $ "Sort mismatch 2:\n" ++ show sortAnnotation' ++ "\n" ++ show argA' ++ "\n" ++ show argA ++ "\n" ++ show a
  | otherwise = annotationApplyLambda env sortEnv s a args (argumentFlatten argA' : aSubst) (annotationArgumentMapping sortRegion argR : rSubst)
  where
    argA' = snd <$> annotationArgumentNormalize env sortEnv sortAnnotation argA
annotationApplyLambda env sortEnv s a args [] [] = Just (s, a, args)
annotationApplyLambda env sortEnv s a args aSubst rSubst
  | not $ sortCompare (ArgumentValue s) (annotationCheckSort env sortEnv [] a') = error "Sort error before substitute"
  | otherwise = Just (s, a', args)
  where
    a' = annotationSubstitute aSubst rSubst a

annotationSubstitute :: [[Annotation]] -> [[RegionVar]] -> Annotation -> Annotation
annotationSubstitute substitutionAnnotation substitutionRegion = annotationSubstitute' substitutionAnnotation substitutionRegion 1 0

annotationSubstitute' :: [[Annotation]] -> [[RegionVar]] -> Int -> Int -> Annotation -> Annotation
annotationSubstitute' substitutionAnnotation substitutionRegion = \x y a -> substitute x y $ a
  where
    count = length substitutionAnnotation -- should be equal to `length substitutionRegion`

    substitute :: Int -> Int -> Annotation -> Annotation
    substitute firstLambda forallNesting (AFix fixRegions sort a) = AFix fixRegions sort $ substitute firstLambda forallNesting <$> a
    substitute firstLambda forallNesting (ATuple as) = ATuple $ map (substitute firstLambda forallNesting) as
    substitute firstLambda forallNesting (AProject a idx) = AProject (substitute firstLambda forallNesting a) idx
    substitute firstLambda forallNesting (AForall a) = AForall $ substitute firstLambda (forallNesting + 1) a
    substitute firstLambda forallNesting x@(ALam argAnnotation argRegion dir a) =
      ALam argAnnotation argRegion dir $ substitute (firstLambda + 1) forallNesting a
    substitute firstLambda forallNesting (AApp a argA argR dir) =
      AApp
        (substitute firstLambda forallNesting a)
        (fmap (substitute firstLambda forallNesting) argA)
        (fmap (substituteRegionVar firstLambda) argR)
        dir
    substitute firstLambda forallNesting (AInstantiate a tp) = AInstantiate (substitute firstLambda forallNesting a) tp
    substitute firstLambda forallNesting (AVar var)
      | lambdaIndex < firstLambda = AVar var
      | lambdaIndex >= firstLambda + count = AVar $ variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = annotationIncrementScope (firstLambda - 1) forallNesting $ (substitutionAnnotation !!! (lambdaIndex - firstLambda)) !!! argumentIndex
      where
        lambdaIndex = indexBoundLambda var
        argumentIndex = indexInArgument var
    substitute firstLambda forallNesting (ARelation cs)
      | null cs' = ABottom
      | otherwise = ARelation cs'
      where
        cs' = mapMaybe f cs
        f (Outlives r1 r2)
          | r1' == r2' = Nothing
          | r1' == regionGlobal = Nothing
          | r2' == regionBottom = Nothing
          | r1' == regionBottom = error "annotationSubstitute: bottom used on wrong side of >="
          | otherwise = Just $ Outlives r1' r2'
          where
            r1' = substituteRegionVar firstLambda r1
            r2' = substituteRegionVar firstLambda r2
    substitute firstLambda forallNesting ABottom = ABottom
    substitute firstLambda forallNesting (AJoin a1 a2) = substitute firstLambda forallNesting a1 `AJoin` substitute firstLambda forallNesting a2

    substituteRegionVar :: Int -> RegionVar -> RegionVar
    substituteRegionVar firstLambda var
      | lambdaIndex < firstLambda = var
      | lambdaIndex >= firstLambda + count = variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = variableIncrementLambdaBound 1 (firstLambda - 1) $ (substitutionRegion !!! (lambdaIndex - firstLambda)) !!! argumentIndex
      where
        lambdaIndex = indexBoundLambda var
        argumentIndex = indexInArgument var

annotationInstantiate :: EffectEnvironment -> SortEnv -> TypeInstantiation -> Sort -> Annotation -> Argument (Sort, Annotation)
annotationInstantiate env sortEnv inst sort annotation
  | not $ sortCompare (ArgumentValue sort) $ annotationCheckSort env sortEnv [] annotation = error "annotationInstantiate: input not correct"
  | otherwise = annotationArgumentInstantiate env sortEnv inst [] $ ArgumentValue (sort, annotation)

type InstantiateVariableSubstitution = [([Argument (Sort, Int)], [Argument Int])]
annotationInstantiate' :: EffectEnvironment -> SortEnv -> TypeInstantiation -> InstantiateVariableSubstitution -> Annotation -> Maybe (Argument (Sort, Annotation))
annotationInstantiate' env sortEnv inst args (AFix _ _ _) = error "cannot instantiate a fixpoint yet"
annotationInstantiate' env sortEnv inst args (AForall a)
  = fmap f <$> annotationInstantiate' env (sortEnvIncrement sortEnv) (typeInstantiationIncrement inst) args a
  where
    f (s, a') = (SortForall s, AForall a')
annotationInstantiate' env sortEnv inst args (ATuple as) = error "annotationInstantiate': Did not expect a tuple here"
annotationInstantiate' env sortEnv inst args (AProject a idx) = case annotationInstantiate' env sortEnv inst args a of
  Nothing -> Nothing
  Just (ArgumentList as) -> Just $ as !! idx
annotationInstantiate' env sortEnv inst args (ALam argA argR dir a) = fmap f <$> annotationInstantiate' env sortEnv' inst args' a
  where
    f (s, a') = (SortFun argA' argR' dir s, ALam argA' argR' dir a')

    argA' = instantiateArgumentType' env inst argA
    argR' = instantiateArgumentType' env inst argR

    (_, substA) = substitution 0 (argA, argA')
    (_, substR) = substitution 0 (argR, argR')

    args' = (substA, map (fmap snd) substR) : args
    sortEnv' = argumentFlatten argA' : sortEnv

    substitution :: Int -> (Argument a, Argument a) -> (Int, [Argument (a, Int)])
    substitution fresh (ArgumentValue _, arg) = return <$> argumentIndex fresh arg
    substitution fresh (ArgumentList args1, ArgumentList args2) = fmap concat $ mapAccumL substitution fresh $ zip args1 args2

    argumentIndex :: Int -> Argument a -> (Int, Argument (a, Int))
    argumentIndex fresh (ArgumentValue a) = (fresh + 1, ArgumentValue (a, fresh))
    argumentIndex fresh (ArgumentList args) = ArgumentList <$> mapAccumL argumentIndex fresh args
annotationInstantiate' env sortEnv inst args (AApp a argA argR dir) = fmap f <$> annotationInstantiate' env sortEnv inst args a
  where
    f (SortFun sortA sortR _ s, a') = (s, AApp a' argA'' argR' dir)
      where
        -- argA is not normalized, so may have a shape which does not match sortA.
        -- We need to convert argA such that its form matches with sortA.
        argA' = annotationsToArgument sortA argA

        argA'' = (\(_, arg) -> maybe ABottom g $ annotationInstantiate' env sortEnv inst args arg) <$> argA'
        argR' = argR >>= lookupRegionVar
    g (ArgumentValue (_, a)) = a
    lookupRegionVar var = case tryIndex args $ indexBoundLambda var - 1 of
      Just (_, regions) -> fmap (variableFromIndices $ indexBoundLambda var) $ regions !!! indexInArgument var
      Nothing -> ArgumentValue var
annotationInstantiate' env sortEnv inst args (AInstantiate a tp) = (>>= f) <$> annotationInstantiate' env sortEnv inst args a
  where
    tp' = tpInstantiate' inst tp

    f :: (Sort, Annotation) -> Argument (Sort, Annotation)
    -- TODO: Should we modify sortEnv in the recursive call?
    -- f (SortForall s, AForall a') = annotationInstantiate env (sortEnv) (TypeInstantiation 0 tp') s a'
    f (SortForall s, a') = annotationToArgument (instantiateType env tp' s) (AInstantiate a' tp')
    f sa = error $ "annotationInstantiate': illegal arguments: " ++ show sa
annotationInstantiate' env sortEnv inst args (AVar var) = case tryIndex args $ indexBoundLambda var - 1 of
  Just (annotations, _) ->
    let
      vars = annotations !!! indexInArgument var
    in
      Just $ fmap (\(s, idx) -> (s, AVar $ variableFromIndices (indexBoundLambda var) idx)) vars
  Nothing ->
    Just $ ArgumentValue (sortEnvLookup sortEnv var, AVar var)
annotationInstantiate' env sortEnv inst args (ARelation constraints)
  | null constraints' = Nothing
  | otherwise = Just $ ArgumentValue (SortRelation, ARelation constraints')
  where
    constraints' = instantiateRelationConstraints f constraints
    f var = case tryIndex args $ indexBoundLambda var - 1 of
      Just (_, regions) -> case regions !!! indexInArgument var of
        args -> map (variableFromIndices $ indexBoundLambda var) $ argumentFlatten args
      Nothing -> [var]
annotationInstantiate' env sortEnv inst args ABottom = Nothing
annotationInstantiate' env sortEnv inst args (AJoin a1 a2) = case annotationInstantiate' env sortEnv inst args a1 of
  Nothing -> annotationInstantiate' env sortEnv inst args a2
  Just as1 -> case annotationInstantiate' env sortEnv inst args a2 of
    Nothing -> Just as1
    Just as2 -> Just $ zipArgument (\(s, a1') (_, a2') -> (s, AJoin a1' a2')) as1 as2

annotationArgumentInstantiate :: EffectEnvironment -> SortEnv -> TypeInstantiation -> InstantiateVariableSubstitution -> Argument (Sort, Annotation) -> Argument (Sort, Annotation)
annotationArgumentInstantiate env sortEnv inst args annotationArgs = annotationArgs >>= f
  where
    f :: (Sort, Annotation) -> Argument (Sort, Annotation)
    f (sort, annotation) = case annotationInstantiate' env sortEnv inst args annotation of
      Just annotations
        | (fst <$> annotations) /= instantiateType' env inst sort -> error $ "Sort error:\n" ++ show (fst <$> annotations) ++ "\n" ++ show (instantiateType' env inst sort) ++ "\n" ++ show annotationArgs
        | otherwise -> annotations
      Nothing -> (\s -> (s, ABottom)) <$> instantiateType' env inst sort

annotationsToArgument :: Argument Sort -> Argument Annotation -> Argument (Sort, Annotation)
annotationsToArgument sorts (ArgumentValue a) = annotationToArgument sorts a
annotationsToArgument (ArgumentList sorts) (ArgumentList as) = ArgumentList $ zipWith annotationsToArgument sorts as

annotationToArgument :: Argument Sort -> Annotation -> Argument (Sort, Annotation)
annotationToArgument (ArgumentValue s) a = ArgumentValue (s, a)
annotationToArgument (ArgumentList sorts) a = ArgumentList $ zipWith f sorts [0..]
  where
    f s idx = annotationToArgument s $ AProject a idx

-- Returns a list of annotations representing (multivariate) applications (or instantiations)
-- The target of the application is psi_1_0
{- annotationFindApplications :: Annotation -> [(Int, Int, [ApplicationOrInstantiation])]
annotationFindApplications = find 0 0
  where
    find :: Int -> Int -> Annotation -> [(Int, Int, [ApplicationOrInstantiation])]
    find scope foralls (AForall a) = find scope (foralls + 1) a
    find scope foralls (ALam _ _ a) = find (scope + 1) foralls a
    find scope foralls (AJoin a1 a2) = find scope foralls a1 ++ find scope foralls a2
    find scope foralls a = case gatherApplications a [] of
      (_, []) -> []
      (AVar var, aoi)
        | indexBoundLambda var == scope + 1 -> [(scope, foralls, aoi)]
      (_, aoi) -> aoi >>= aoiFlattenAnnotations >>= find scope foralls
-}

gatherApplications :: Annotation -> [ApplicationOrInstantiation] -> (Annotation, [ApplicationOrInstantiation])
gatherApplications (AInstantiate a tp) args = gatherApplications a (AOIInstantiation tp : args)
gatherApplications (AApp a argA argR dir) args = gatherApplications a (AOIApplication argA argR dir : args)
gatherApplications a args = (a, args)

data ApplicationOrInstantiation
  = AOIApplication !(Argument Annotation) !(Argument RegionVar) RegionDirection
  | AOIInstantiation !Tp
  
instance Show ApplicationOrInstantiation where
  show (AOIApplication argA argR dir) = "[" ++ show argA ++ "; " ++ show argR ++ "]" ++ show dir
  show (AOIInstantiation tp) = "{ " ++ show tp ++ " }"

aoiMapAnnotation :: (Annotation -> Annotation) -> ApplicationOrInstantiation -> ApplicationOrInstantiation
aoiMapAnnotation f (AOIApplication a r dir) = AOIApplication (fmap f a) r dir
aoiMapAnnotation _ (AOIInstantiation tp) = AOIInstantiation tp

aoiFlattenAnnotations :: ApplicationOrInstantiation -> [Annotation]
aoiFlattenAnnotations (AOIApplication a _ _) = argumentFlatten a
aoiFlattenAnnotations _ = []

aoiIncrementLambdaScope :: Int -> ApplicationOrInstantiation -> ApplicationOrInstantiation
aoiIncrementLambdaScope inc (AOIApplication a r dir) = AOIApplication (annotationIncrementScope inc 0 <$> a) (variableIncrementLambdaBound 1 inc <$> r) dir
aoiIncrementLambdaScope _ (AOIInstantiation tp) = AOIInstantiation tp

-- Iterates a saturated fixpoint annotation of the form `(fix(_regions) (psi_1) psi_2) [\hat{\psi}; \hat{\rho}] ..`, of kind *.
-- Bool in return type denotes whether the result is a higher order fixpoint
annotationIterate :: EffectEnvironment -> SortEnv -> FixRegions -> Argument Sort -> Argument Annotation -> [ApplicationOrInstantiation] -> Argument (Bool, Sort, Annotation)
annotationIterate _ _ _ _ (ArgumentList []) _ = ArgumentList []
annotationIterate env sortEnv (FixRegionsEscape arity regions) sorts initial application
  = fmap f $ annotationFixpointElements $ snd $ annotationIterateEscape env sortEnv arity regions sorts initial
  where
    f (True, s, a) = (True, s, a)
    f (False, s, a) =
      -- First order fixpoint, continue using the fixpoint iteration
      -- With fix regions none, we might be able to evaluate the fixpoint further
      let
        ArgumentValue a' = annotationNormalize env sortEnv (ArgumentValue s) a
        -- ArgumentValue res = annotationIterate env sortEnv FixRegionsNone (ArgumentValue s) (ArgumentValue a) application
      in if sortCompare (ArgumentValue s) (annotationCheckSort env sortEnv [] a) then
        (True, s, a')
        else error "sort error"
annotationIterate env sortEnv FixRegionsNone (ArgumentValue sort) (ArgumentValue initial) application =
  let (h, a) = iterate 0 initial
  in ArgumentValue (h, sort, a)
  where
    sort' = SortFun (ArgumentValue sort) argumentEmpty RegionDirectionAny sort
    bottom = ArgumentValue ABottom

    application' = aoiIncrementLambdaScope 1 <$> application

    recursiveArgument = ArgumentValue $ AVar $ variableFromIndices 1 0
    sortEnvBody = [sort] : sortEnv

    iterate :: Int -> Annotation -> (Bool, Annotation)
    iterate 6 _ = error "annotationIterate: probably infinite recursion"
    iterate iteration current =
      case isFixed iteration current next of
        HigherOrderFixpoint -> (True, applyWith sortEnv ABottom current)
        FirstOrderFixpoint ->
          let ArgumentValue next' = annotationNormalize env sortEnv (ArgumentValue $ SortFun (ArgumentValue sort) argumentEmpty RegionDirectionAny sort) $ annotationInlineConstantArguments sort next application
          in
            if applyWith sortEnv ABottom next == applyWith sortEnv ABottom next'
            then (False, AFix FixRegionsNone (ArgumentValue sort) $ ArgumentValue next)
            else iterate (iteration + 1) next'
          -- error "first order fixpoint"
        NoFixpoint
          | sortCompare (ArgumentValue sort') $ annotationCheckSort env sortEnv [] next
            -> iterate (iteration + 1) next
          | otherwise -> error "sort error in iteration"
      where
        next = iterateNext current current

    isFixed :: Int -> Annotation -> Annotation -> FixpointState
    isFixed iteration arg1 arg2
      | arg1' == arg2' = HigherOrderFixpoint
      | firstOrder arg1 == firstOrder arg2 = FirstOrderFixpoint
      | otherwise = NoFixpoint
      where
        arg1' = applyWith sortEnv ABottom arg1
        arg2' = applyWith sortEnv ABottom arg2
        firstOrder :: Annotation -> Annotation
        firstOrder a = let ArgumentValue a' = annotationNormalize env sortEnv (ArgumentValue sort) $ annotationToFirstOrder a in a'

    iterateNext :: Annotation -> Annotation -> Annotation
    iterateNext with a
      = ALam (ArgumentValue sort) argumentEmpty RegionDirectionAny $ applyWith sortEnvBody with' (annotationIncrementScope 1 0 a)
      where
        with' = AApp (annotationIncrementScope 1 0 with) recursiveArgument argumentEmpty RegionDirectionAny

    applyWith :: SortEnv -> Annotation -> Annotation -> Annotation
    applyWith sortEnv' with a =
      let
        ArgumentValue a' = annotationNormalize env sortEnv' (ArgumentValue sort) $ AApp a (ArgumentValue with) argumentEmpty RegionDirectionAny
      in
        a'
annotationIterate env sortEnv FixRegionsNone sorts functions application = f <$> functions''
  where
    sorts' = SortFun sorts argumentEmpty RegionDirectionAny <$> sorts
    functions' = snd <$> annotationArgumentNormalize env sortEnv sorts' functions
    functions'' = annotationFixpointElements $ zipArgument g sorts functions'

    g s ABottom = (True, s, ABottom)
    g s a@(ALam _ _ _ a')
      | not $ annotationHasUnboundAnnotationVar True 1 a' = (True, s, annotationIncrementScope (-1) 0 a')
    g s a = (False, s, a)

    f (True, s, a) = (True, s, a)
    f (False, _, AFix FixRegionsNone s a) =
      let
        ArgumentValue res = annotationIterate env sortEnv FixRegionsNone s a application
      in res

annotationSplitRecursiveApplications :: Int -> Annotation -> (Annotation, [[ApplicationOrInstantiation]])
annotationSplitRecursiveApplications scope = split
  where
    split :: Annotation -> (Annotation, [[ApplicationOrInstantiation]])
    split (AJoin a1 a2) =
      case getRecursiveApplication a1 [] of
        Just app -> (app:) <$> split a2
        Nothing -> case split a2 of
          (ABottom, apps) -> (a1, apps)
          (a2', apps) -> (AJoin a1 a2', apps)
    split a = case getRecursiveApplication a [] of
      Just app -> (ABottom, [app])
      Nothing -> (a, [])

    getRecursiveApplication :: Annotation -> [ApplicationOrInstantiation] -> Maybe [ApplicationOrInstantiation]
    getRecursiveApplication (AVar var) args
      | var == variableFromIndices scope 0 = Just args
    getRecursiveApplication (AApp a argA argR lifetimeContext) args = getRecursiveApplication a (AOIApplication argA argR lifetimeContext : args)
    getRecursiveApplication (AInstantiate a tp) args = getRecursiveApplication a (AOIInstantiation tp : args)
    getRecursiveApplication _ _ = Nothing

annotationIterateEscape :: EffectEnvironment -> SortEnv -> Int -> Argument SortArgumentRegion -> Argument Sort -> Argument Annotation -> ([RegionVar], Argument (Bool, Sort, Annotation))
annotationIterateEscape env sortEnv arity regions sorts functions = iterate 0 bottom
  where
    bottom = ABottom <$ sorts

    regionCount = length $ argumentFlatten regions

    iterate :: Int -> Argument Annotation -> ([RegionVar], Argument (Bool, Sort, Annotation))
    iterate 10 current = error "annotationIterateEscape: Probably no fixpoint."
    iterate idx current
      | current == next6 =
        ( mapping'
        , zipArgument (\s a -> (True, s, a)) sorts current
        )
      | fmap annotationToFirstOrder current == fmap annotationToFirstOrder next6 =
        ( mapping'
        , applyMapping mapping' arity sorts next6 functions
        )
      | otherwise = iterate (idx + 1) next6
      where
        next1 = (\a -> AApp a current argumentEmpty RegionDirectionAny) <$> functions
        next2 = annotationArgumentNormalize env sortEnv sorts next1
        (mapping, next3) = annotationCollapse regions arity $ fmap snd next2
        next4 = annotationArgumentNormalize env sortEnv sorts next3
        (escapes, next5) = annotationFilterInternalRegions $ fmap snd next4
        next6 = snd <$> annotationArgumentNormalize env sortEnv sorts next5

        mapping' = map getRegionVar [0 .. regionCount - 1]
        getRegionVar idx
          | indexBoundLambda unified == scope && indexInArgument unified `IntSet.notMember` escapes = regionBottom
          | otherwise = unified
          where
            scope = arity + 3
            unified = maybe (variableFromIndices scope idx) RegionVar $ IntMap.lookup idx mapping

    applyMapping :: [RegionVar] -> Int -> Argument Sort -> Argument Annotation -> Argument Annotation -> Argument (Bool, Sort, Annotation)
    applyMapping mapping 0 sorts _ args = zipArgument saturateWithRegions sorts args
      where
        saturateWithRegions :: Sort -> Annotation -> (Bool, Sort, Annotation)
        saturateWithRegions sort annotation = (False, sort, addForallsLambdas 0 0 sort)
          where
            applied = AApp annotation argumentEmpty (ArgumentList $ ArgumentValue <$> mapping) RegionDirectionAny

            -- Adds foralls and lambdas for all remaining arguments
            addForallsLambdas :: Int -> Int -> Sort -> Annotation
            addForallsLambdas lambdas foralls (SortForall s) = AForall $ addForallsLambdas lambdas (foralls + 1) s
            addForallsLambdas lambdas foralls (SortFun sortA sortR dir s) = ALam sortA sortR dir $ addForallsLambdas (lambdas + 1) foralls s
            addForallsLambdas lambdas foralls _ = applications lambdas foralls sort $ annotationIncrementScope lambdas foralls applied

            applications :: Int -> Int -> Sort -> Annotation -> Annotation
            applications lambdas foralls (SortForall s) a = applications lambdas (foralls - 1) s $ AInstantiate a (TpVar $ TypeVar $ foralls - 1)
            applications lambdas foralls (SortFun sortA sortR dir s) a = applications (lambdas - 1) foralls s $ AApp a (AVar <$> sortArgumentToArgument lambdas sortA) (sortArgumentToArgument lambdas sortR) dir
            applications 0 0 _ a = a
            applications _ _ _ _ = error "annotationSaturateWithSort: error in lambda and forall count"
    applyMapping mapping arity' (ArgumentList [ArgumentValue sort, sorts]) (ArgumentList [ArgumentValue partial, restFixed]) (ArgumentList [_, rest])
      = ArgumentList [ArgumentValue (True, sort, partial), applyMapping mapping (arity' - 1) sorts restFixed rest]

annotationFixpointElements :: Argument (Bool, Sort, Annotation) -> Argument (Bool, Sort, Annotation)
annotationFixpointElements args = zipArgument (\(higherOrder, s, _) a -> (higherOrder, s, a)) args $ inlineArgument []
  where
    indices = (\r@RegionVar{} -> indexInArgument r) <$> sortArgumentToArgument 0 args
    list = argumentFlatten args

    inlineArgument :: [Int] -> Argument Annotation
    inlineArgument stack = inline stack <$> indices

    inline :: [Int] -> Int -> Annotation
    inline stack idx = case elemIndex idx stack of
      Just position -> AVar $ variableFromIndices (position + 1) 0
      Nothing -> case list !!! idx of
        (True, _, a) -> a -- Already fixed
        (False, s, a) ->
          let
            a' = annotationIncrementScope (1 + length stack) 0 a
            a'' = AApp a' (inlineArgument (idx : stack)) argumentEmpty RegionDirectionAny
          in
            AFix FixRegionsNone (ArgumentValue s) $ ArgumentValue $ ALam (ArgumentValue s) argumentEmpty RegionDirectionAny $ a''

data FixpointState = NoFixpoint | FirstOrderFixpoint | HigherOrderFixpoint

annotationApplicationHasUnboundAnnotationVar :: Int -> [ApplicationOrInstantiation] -> Bool
annotationApplicationHasUnboundAnnotationVar scope application = any (annotationHasUnboundAnnotationVar False scope) (application >>= aoiFlattenAnnotations)

type IsConstant = [Either Bool (Argument Bool)]
-- Finds which arguments do not change in recursive calls
-- Left denotes whether a quantification is constant, right denotes whether an annotation argument is constant
annotationConstantArguments :: Sort -> Annotation -> IsConstant
annotationConstantArguments sort = check 0 2
  where
    empty :: IsConstant
    empty = emptyForSort sort

    emptyForSort :: Sort -> IsConstant
    emptyForSort (SortFun argA _ _ s) = Right (True <$ argA) : emptyForSort s
    emptyForSort (SortForall s) = Left True : emptyForSort s
    emptyForSort _ = []

    check :: Int -> Int -> Annotation -> IsConstant
    check foralls scope a = joins (map (checkApplication foralls scope) apps) `join` checkNested foralls scope a
      where
        (_, apps) = annotationSplitRecursiveApplications scope a

    checkNested :: Int -> Int -> Annotation -> IsConstant
    checkNested foralls scope (AFix _ _ arg) = checkArgument foralls scope arg
    checkNested foralls scope (AForall a) = check (foralls + 1) scope a
    checkNested foralls scope (ALam _ _ _ a) = check foralls (scope + 1) a
    checkNested foralls scope (AApp a argA _ _) = checkNested foralls scope a `join` checkArgument foralls scope argA
    checkNested foralls scope (AInstantiate a _) = checkNested foralls scope a
    checkNested foralls scope (ATuple as) = joins $ check foralls scope <$> as
    checkNested foralls scope (AProject a _) = check foralls scope a
    checkNested foralls scope (AJoin a1 a2) = checkNested foralls scope a1 `join` checkNested foralls scope a2
    checkNested _ _ _ = empty

    checkArgument :: Int -> Int -> Argument Annotation -> IsConstant
    checkArgument foralls scope = joins . map (check foralls scope) . argumentFlatten 

    checkApplication :: Int -> Int -> [ApplicationOrInstantiation] -> IsConstant
    checkApplication foralls scope = (\(_, _, c) -> c) . checkApp
      where
        checkApp :: [ApplicationOrInstantiation] -> (Int, Int, IsConstant)
        checkApp [] = (foralls, scope, [])
        checkApp (AOIApplication argA _ _ : app) =
          let
            (foralls', scope', constant) = checkApp app
            argA' = AVar <$> sortArgumentToArgument scope argA
          in
            (foralls', scope' + 1, Right (zipArgument (==) argA argA') : constant)
        checkApp (AOIInstantiation tp : app) =
          let
            (foralls', scope', constant) = checkApp app
          in
            (foralls' + 1, scope', Left (TpVar (TypeVar foralls') == tp) : constant)

    joins :: [IsConstant] -> IsConstant
    joins = foldr join empty

    join :: IsConstant -> IsConstant -> IsConstant
    join = zipWith f
      where
        f (Left x) (Left y) = Left $ x && y
        f (Right xs) (Right ys) = Right $ zipArgument (&&) xs ys

annotationInlineConstantArguments :: Sort -> Annotation -> [ApplicationOrInstantiation] -> Annotation
annotationInlineConstantArguments sort lambda@(ALam annotationArgA annotationArgR annotationLifetimeContext annotation) application
  | not hasConstant = lambda
  | otherwise = ALam annotationArgA annotationArgR annotationLifetimeContext $ addForallsLambdas sort application 0 0
  where
    constants = annotationConstantArguments sort annotation

    hasConstant = any f constants
      where
        f (Left c) = c
        f (Right cs) = or $ argumentFlatten cs

    addForallsLambdas :: Sort -> [ApplicationOrInstantiation] -> Int -> Int -> Annotation
    addForallsLambdas _ [] lambdas foralls = call lambdas foralls
    addForallsLambdas (SortFun argA argR lifetimeContext s) (AOIApplication _ _ _ : apps) lambdas foralls
      = ALam argA argR lifetimeContext
      $ addForallsLambdas s apps (lambdas + 1) foralls
    addForallsLambdas (SortForall s) (AOIInstantiation _ : apps) lambdas foralls
      = AForall <$> addForallsLambdas s apps lambdas $ foralls + 1
    
    call :: Int -> Int -> Annotation
    call lambdaCount forallCount
      = addApplications lambdaCount forallCount constants application
        $ ALam annotationArgA annotationArgR annotationLifetimeContext
        $ AApp (annotationIncrementScope (lambdaCount + 1) forallCount lambda)
        (ArgumentValue $ AVar $ variableFromIndices (lambdaCount + 1) 0) argumentEmpty annotationLifetimeContext
      where
        addApplications :: Int -> Int -> IsConstant -> [ApplicationOrInstantiation] -> Annotation -> Annotation
        addApplications lambdas foralls (Left c : constants) (AOIInstantiation tp : apps) a
          = addApplications lambdas (foralls - 1) constants apps $ AInstantiate a tp'
          where
            tp'
              | c = tpIncreaseScope foralls 0 tp
              | otherwise = TpVar $ TypeVar (foralls - 1)
        addApplications lambdas foralls (Right cs : constants) (AOIApplication argA argR lifetimeContext : apps) a
          = addApplications lambdas foralls constants apps $ AApp a argA' argR' lifetimeContext
          where
            argA'' = zipArgument (\c a -> if c then Just $ annotationIncrementScope lambdaCount forallCount a else Nothing) cs argA
            argA' = zipArgument (fromMaybe . AVar) (sortArgumentToArgument lambdas argA) argA''
            argR' = sortArgumentToArgument lambdas argR
        addApplications lambdas foralls [] [] a = a
   -- Checks whether an annotation has unbound annotation variable
annotationHasUnboundAnnotationVar :: Bool -> Int -> Annotation -> Bool
annotationHasUnboundAnnotationVar exact minScope (AFix _ _ arg) = any (annotationHasUnboundAnnotationVar exact minScope) $ argumentFlatten arg
annotationHasUnboundAnnotationVar exact minScope (AForall a) = annotationHasUnboundAnnotationVar exact minScope a
annotationHasUnboundAnnotationVar exact minScope (ATuple as) = any (annotationHasUnboundAnnotationVar exact minScope) as
annotationHasUnboundAnnotationVar exact minScope (AProject a idx) = annotationHasUnboundAnnotationVar exact minScope a
annotationHasUnboundAnnotationVar exact minScope (ALam _ _ _ a) = annotationHasUnboundAnnotationVar exact (minScope + 1) a
annotationHasUnboundAnnotationVar exact minScope (AApp a argA argR _)
  = annotationHasUnboundAnnotationVar exact minScope a
  || any (annotationHasUnboundAnnotationVar exact minScope) (argumentFlatten argA)
annotationHasUnboundAnnotationVar exact minScope (AInstantiate a _) = annotationHasUnboundAnnotationVar exact minScope a
annotationHasUnboundAnnotationVar exact minScope (AVar var) = indexBoundLambda var `op` minScope
  where
    op = if exact then (==) else (>=)
annotationHasUnboundAnnotationVar exact minScope (AJoin a1 a2)
  = annotationHasUnboundAnnotationVar exact minScope a1
  || annotationHasUnboundAnnotationVar exact minScope a2
annotationHasUnboundAnnotationVar _ _ _ = False

-- Substitutes all free variables with bottom
-- Assumes that all fixpoints are in a first order fixpoint
annotationToFirstOrder :: Annotation -> Annotation
annotationToFirstOrder (AFix fixRegions sort arguments) = annotationToFirstOrder $ argumentToAnnotation $ f <$> arguments
  where
    f :: Annotation -> Annotation
    f ABottom = ABottom
    f (ALam _ _ _ a) = annotationSubstitute [bottoms] [] a
    bottoms = argumentFlatten $ ABottom <$ sort
annotationToFirstOrder (ALam argA argR dir a) = ALam argA argR dir $ annotationToFirstOrder a
annotationToFirstOrder (AForall a) = AForall $ annotationToFirstOrder a
annotationToFirstOrder (AApp a argA argR lifetimeContext) = case annotationToFirstOrder a of
  ABottom -> ABottom
  a' -> AApp a (annotationToFirstOrder <$> argA) argR lifetimeContext
annotationToFirstOrder (AInstantiate a tp) = AInstantiate (annotationToFirstOrder a) tp
annotationToFirstOrder (ATuple as) = ATuple $ annotationToFirstOrder <$> as
annotationToFirstOrder (AProject a idx) = AProject (annotationToFirstOrder a) idx
annotationToFirstOrder (AJoin a1 a2) = AJoin (annotationToFirstOrder a1) (annotationToFirstOrder a2)
annotationToFirstOrder (AVar _) = ABottom
annotationToFirstOrder a = a

annotationArgumentRemoveUnusedRegionArguments :: Argument Annotation -> ([Maybe Int], Argument Annotation)
annotationArgumentRemoveUnusedRegionArguments arguments@(ArgumentList []) = ([], arguments)
annotationArgumentRemoveUnusedRegionArguments arguments = (mapping, fmap substitute arguments)
  where
    used = IntSet.unions $ map (annotationUsedRegionVariables True) $ argumentFlatten arguments

    regions = case filter (ABottom /=) $ argumentFlatten arguments of
      ALam _ (ArgumentList regions) _ _ : _ -> regions
      [] -> []
      a -> error $ "annotationArgumentRemoveUnusedRegionArguments: expected lambda, got " ++ show a

    mapping = assignIndices 0 0
    regionCount = length regions
    newRegionCount = length $ filter isJust mapping

    assignIndices :: Int -> Int -> [Maybe Int]
    assignIndices fresh idx
      | idx >= regionCount = []
      | idx `IntSet.member` used = Just fresh : assignIndices (fresh + 1) (idx + 1)
      | otherwise = Nothing : assignIndices fresh (idx + 1) -- Region not used

    substitution = map (maybe regionBottom (variableFromIndices 1)) mapping
    substitute (ALam (ArgumentList []) _ dir a) = ALam
      (ArgumentList [])
      (ArgumentList $ replicate newRegionCount $ ArgumentValue SortArgumentRegionMonomorphic)
      dir
      $ annotationSubstitute' [[]] [substitution] 1 0 $ annotationIncrementScope' 1 0 2 0 a
    substitute ABottom = ABottom
    substitute a = error $ "annotationArgumentRemoveUnusedRegionArguments: expected lambda, got " ++ show a

type SortEnv = [[Sort]]

-- Increments the scope of type variables in the sort environment
sortEnvIncrement :: SortEnv -> SortEnv
sortEnvIncrement = fmap $ fmap $ sortIncreaseScope 1 0

sortEnvLookup :: SortEnv -> AnnotationVar -> Sort
sortEnvLookup env var = case tryIndex env $ indexBoundLambda var - 1 of
  Nothing -> error $ "sortEnvLookup: Variable " ++ show var ++ " not found in sort environment " ++ show env
  Just sorts -> case tryIndex sorts $ indexInArgument var of
    Nothing -> error $ "sortEnvLookup: Variable " ++ show var ++ " not found. Cannot index this variable in argument."
    Just s -> s

annotationSaturateHead :: Sort -> Annotation -> Annotation
annotationSaturateHead _ a@ALam{} = a
annotationSaturateHead _ a@AInstantiate{} = a
annotationSaturateHead annotationSort annotation = addForallsLambdas 0 0 annotationSort
  where
    -- Adds foralls and lambdas for all remaining arguments
    addForallsLambdas :: Int -> Int -> Sort -> Annotation
    addForallsLambdas lambdas foralls (SortForall s) = AForall $ addForallsLambdas lambdas (foralls + 1) s
    addForallsLambdas lambdas foralls (SortFun sortA sortR dir s) = ALam sortA sortR dir $ addForallsLambdas (lambdas + 1) foralls s
    addForallsLambdas lambdas foralls _ = applications lambdas foralls annotationSort (annotationIncrementScope lambdas foralls annotation)

    applications :: Int -> Int -> Sort -> Annotation -> Annotation
    applications lambdas foralls (SortForall s) a = applications lambdas (foralls - 1) s $ AInstantiate a (TpVar $ TypeVar $ foralls - 1)
    applications lambdas foralls (SortFun sortA sortR dir s) a = applications (lambdas - 1) foralls s $ AApp a (AVar <$> sortArgumentToArgument lambdas sortA) (sortArgumentToArgument lambdas sortR) dir
    applications 0 0 _ a = a
    applications _ _ _ _ = error "annotationSaturateWithSort: error in lambda and forall count"

annotationArgumentCheckSort :: EffectEnvironment -> SortEnv -> RegionEnv -> Argument Annotation -> Argument (Maybe Sort)
annotationArgumentCheckSort env sortEnv regionEnv arg = arg >>= annotationCheckSort env sortEnv regionEnv

type RegionEnv = [[(SortArgumentRegion, RegionDirection)]]
regionEnvIncrement :: RegionEnv -> RegionEnv
regionEnvIncrement = fmap $ fmap f
  where
    f (SortArgumentRegionMonomorphic, dir) = (SortArgumentRegionMonomorphic, dir)
    f (SortArgumentRegionPolymorphic (TypeVar idx) tps, dir) = (SortArgumentRegionPolymorphic (TypeVar $ idx + 1) (tpIncreaseScope 1 0 <$> tps), dir)

annotationCheckSort' :: EffectEnvironment -> SortEnv -> RegionEnv -> Annotation -> Argument (Maybe Sort)
annotationCheckSort' env sortEnv regionEnv a = annotationCheckSort env sortEnv regionEnv a

annotationCheckSort :: EffectEnvironment -> SortEnv -> RegionEnv -> Annotation -> Argument (Maybe Sort)
annotationCheckSort env sortEnv regionEnv (AFix _ sort args)
  | sortCompare (SortFun sort argumentEmpty RegionDirectionAny <$> sort) sortBody = Just <$> sort
  | otherwise = error $ "Sort of fix combinator does not match body.\nFix: " ++ show sort ++ "\nBody: " ++ show sortBody
  where
    sortBody = annotationArgumentCheckSort env sortEnv regionEnv args
annotationCheckSort env sortEnv regionEnv (AForall a) = fmap SortForall <$> annotationCheckSort env (sortEnvIncrement sortEnv) (regionEnvIncrement regionEnv) a
annotationCheckSort env sortEnv regionEnv (ALam argA argR dir a) = fmap (SortFun argA argR dir) <$> annotationCheckSort env sortEnv' regionEnv' a
  where
    sortEnv' = argumentFlatten argA : sortEnv
    regionEnv' = ((\s -> (s, dir)) <$> argumentFlatten argR) : regionEnv
annotationCheckSort env sortEnv regionEnv (AApp a argA argR dir) = fmap f <$> annotationCheckSort env sortEnv regionEnv a
  where
    f (SortFun sortA sortR dir' s)
      | dir /= dir' = error "Region directions do not match"
      | not $ sortCompare sortA argSort = error $ "Sort of argument in application does not match.\nFunction sort: " ++ show sortA ++ "\nArgument sort: " ++ show argSort
      | not $ regionArgumentCompare (show (length sortEnv, length regionEnv)) regionEnv dir sortR argR = error $ "Sort of region argument in application does not match.\nFunction sort: " ++ show sortR ++ "\nArgument: " ++ show argR ++ "\nRegion env: " ++ {- show regionEnv ++ -} "\n" ++ show (length sortEnv)
      | otherwise = s
      where
        argSort = annotationArgumentCheckSort env sortEnv regionEnv argA
    f s = error $ "Expected sort forall, got " ++ show s
annotationCheckSort env sortEnv regionEnv (AInstantiate a tp) = annotationCheckSort env sortEnv regionEnv a >>= f
  where
    f (Just (SortForall s)) = Just <$> instantiateType env tp s
    f Nothing = ArgumentValue Nothing
annotationCheckSort env sortEnv regionEnv (ATuple as) = ArgumentList $ map (annotationCheckSort env sortEnv regionEnv) as
annotationCheckSort env sortEnv regionEnv (AProject a idx) = case annotationCheckSort env sortEnv regionEnv a of
  ArgumentList sorts -> sorts !!! idx
  ArgumentValue Nothing -> ArgumentValue Nothing
  ArgumentValue s -> error $ "Extected argument list in extract(..), got singular sort " ++ show s
annotationCheckSort env sortEnv regionEnv (AVar var) = ArgumentValue $ Just $ sortEnvLookup sortEnv var
annotationCheckSort env sortEnv regionEnv (ARelation cs)
  | all exist2 cs = ArgumentValue $ Just SortRelation
  | otherwise = error $ "Relation has undeclared region variables: " ++ show cs ++ "\n" ++ {-show regionEnv ++-} "\n" ++ show (filter (not . exist2) cs)
  where
    exist2 (Outlives r1 r2) = exist r1 && exist r2
    exist (RegionVar 0) = True
    exist r = case tryIndex regionEnv (indexBoundLambda r - 1) of
      Nothing -> indexBoundLambda r >= 1 -- Ignore, we do not have a region environment available in annotationNormalize
      Just rs -> indexInArgument r >= 0 && indexInArgument r < length rs
annotationCheckSort env sortEnv regionEnv ABottom = ArgumentValue Nothing
annotationCheckSort env sortEnv regionEnv (AJoin a1 a2)
  | sortCompare' s1 s2 = sortJoin s1 s2
  | otherwise = error $ "Sorts in a join are not the same:\n" ++ show s1 ++ "\n" ++ show s2 ++ "\n" ++ show a1 ++ "\n" ++ show a2
  where
    s1 = annotationCheckSort env sortEnv regionEnv a1
    s2 = annotationCheckSort env sortEnv regionEnv a2

regionArgumentCompare :: String -> RegionEnv -> RegionDirection -> Argument SortArgumentRegion -> Argument RegionVar -> Bool
regionArgumentCompare str env dir (ArgumentValue s1) (ArgumentValue var) = case regionEnvLookup str env var of
  Just (s2, dir2)
    | not $ dir == dir2 || dir2 == RegionDirectionAny -> False
    | s1 == s2 -> True
    | otherwise -> case (s1, s2) of
      (SortArgumentRegionPolymorphic _ _, SortArgumentRegionMonomorphic) -> True
      _ -> False
  Nothing -> True
regionArgumentCompare str env dir (ArgumentList _) (ArgumentValue var) = case regionEnvLookup str env var of
  Just (s2, dir2) -> s2 == SortArgumentRegionMonomorphic && (dir == dir2 || dir2 == RegionDirectionAny)
  Nothing -> True
regionArgumentCompare str env dir (ArgumentList sorts) (ArgumentList rs) =
  length sorts == length rs && all (uncurry $ regionArgumentCompare str env dir) (zip sorts rs)
regionArgumentCompare _ _ _ _ _ = False

regionEnvLookup :: String -> RegionEnv -> RegionVar -> Maybe (SortArgumentRegion, RegionDirection)
regionEnvLookup str env var = case tryIndex env (indexBoundLambda var - 1) of
  Nothing -> Nothing
  Just sorts -> case tryIndex sorts (indexInArgument var) of
    Nothing -> error $ str ++ "Region sort error: could not find variable " ++ show var ++ " in region env " ++ show env
    Just s -> Just s

sortCompare' :: Argument (Maybe Sort) -> Argument (Maybe Sort) -> Bool
sortCompare' (ArgumentList as) (ArgumentList bs)
  | length as == length bs = all (uncurry sortCompare') (zip as bs)
  | otherwise = error $ "Wrong lengths\n" ++ show as ++ "\n" ++ show bs
sortCompare' (ArgumentValue (Just s1)) (ArgumentValue (Just s2)) = if s1 == s2 then True else error $ "Wrong2\n" ++ show s1 ++ "\n" ++ show s2
sortCompare' (ArgumentValue Nothing) _ = True
sortCompare' _ (ArgumentValue Nothing) = True
sortCompare' s1 s2 = error $ "Wrong\n" ++ show s1 ++ "\n" ++ show s2

sortCompare :: Argument Sort -> Argument (Maybe Sort) -> Bool
sortCompare = sortCompare' . fmap Just

sortJoin :: Argument (Maybe Sort) -> Argument (Maybe Sort) -> Argument (Maybe Sort)
sortJoin (ArgumentList as) (ArgumentList bs) = ArgumentList $ uncurry sortJoin <$> zip as bs
sortJoin (ArgumentValue (Just s1)) _ = ArgumentValue $ Just s1
sortJoin _ (ArgumentValue (Just s2)) = ArgumentValue $ Just s2
sortJoin _ _ = ArgumentValue Nothing

annotationCollapse :: Argument SortArgumentRegion -> Int -> Argument Annotation -> (IntMap Int, Argument Annotation)
annotationCollapse sortRegions arity arguments = (mapping, substitute 0 <$> arguments)
  where
    argumentMain : argumentsRest = drop (arity - 1) $ argumentFlatten arguments

    baseRelation = relationFromTransitiveConstraints $ annotationBaseRelation argumentMain
    regionsHigherOrderUse =
      annotationUsedRegionVariables True (annotationRemoveBaseRelation argumentMain)
      `IntSet.union` IntSet.unions (annotationUsedRegionVariables True <$> argumentsRest)

    canCollapse var@(RegionVar idx) = indexBoundLambda var == arity + 3 && IntSet.notMember (indexInArgument var) regionsHigherOrderUse
    mapping = relationCollapse canCollapse baseRelation

    substitute :: Int -> Annotation -> Annotation
    substitute lambdaCount (AFix regions sort a) = AFix regions sort $ substitute lambdaCount <$> a
    substitute lambdaCount (AForall a) = AForall $ substitute lambdaCount a
    substitute lambdaCount (ALam argA argR dir a) = ALam argA argR dir $ substitute (lambdaCount + 1) a
    substitute lambdaCount (AApp a argA argR dir) = AApp (substitute lambdaCount a) (substitute lambdaCount <$> argA) (substituteRegionVar lambdaCount <$> argR) dir
    substitute lambdaCount (AInstantiate a tp) = AInstantiate (substitute lambdaCount a) tp
    substitute lambdaCount (ATuple as) = ATuple (substitute lambdaCount <$> as)
    substitute lambdaCount (AProject a idx) = AProject (substitute lambdaCount a) idx
    substitute lambdaCount (ARelation cs) = case mapMaybe (substituteRelationConstraint lambdaCount) cs of
      [] -> ABottom
      cs' -> ARelation $ sort cs'
    substitute lambdaCount (AJoin a1 a2) = AJoin (substitute lambdaCount a1) (substitute lambdaCount a2)
    substitute _ (AVar var) = AVar var
    substitute _ ABottom = ABottom

    substituteRelationConstraint :: Int -> RelationConstraint -> Maybe RelationConstraint
    substituteRelationConstraint lambdaCount (Outlives r1 r2) = case (substituteRegionVar' lambdaCount r1, substituteRegionVar' lambdaCount r2) of
      (Just r1', Just r2')
        | r2' == regionBottom -> Nothing
        | r1' == r2' -> Nothing
        | r1' == regionGlobal -> Nothing
        | r1' == regionBottom -> error "annotationCollapse: bottom used on wrong side of >="
        | otherwise -> Just $ Outlives r1' r2'
      _ -> Nothing
      where
        r1' = substituteRegionVar' lambdaCount r1
        r2' = substituteRegionVar' lambdaCount r2

    substituteRegionVar' :: Int -> RegionVar -> Maybe RegionVar
    substituteRegionVar' lambdaCount r1 = case IntMap.lookup idx mapping of
      Nothing -> Just r1
      Just r2
        | indexBoundLambda (RegionVar r2) + lambdaCount - arity - 3 <= 1 && indexBoundLambda (RegionVar r2) /= 0
          -> Nothing
        | otherwise -> Just $ variableIncrementLambdaBound 1 (lambdaCount - arity - 3) $ RegionVar r2
      where
        RegionVar idx = variableIncrementLambdaBound 1 (arity + 3 - lambdaCount) r1

    substituteRegionVar :: Int -> RegionVar -> RegionVar
    substituteRegionVar lambdaCount r1 = case IntMap.lookup idx mapping of
      Nothing -> r1
      Just r2 -> variableIncrementLambdaBound 1 (lambdaCount - arity - 3) $ RegionVar r2
      where
        RegionVar idx = variableIncrementLambdaBound 1 (arity + 3 - lambdaCount) r1

argumentToAnnotation :: Argument Annotation -> Annotation
argumentToAnnotation (ArgumentValue a) = a
argumentToAnnotation (ArgumentList as) = ATuple $ map argumentToAnnotation as

annotationIsLambdaOrBottom :: Annotation -> Bool
annotationIsLambdaOrBottom ABottom = True
annotationIsLambdaOrBottom ALam{} = True
annotationIsLambdaOrBottom _ = False

annotationRemoveUnusedFixpoints :: Annotation -> Annotation
annotationRemoveUnusedFixpoints = snd . transform 0
  where
    transform :: Int -> Annotation -> (IntSet, Annotation)
    transform lambdas (AFix FixRegionsNone sorts args)
      | all annotationIsLambdaOrBottom $ argumentFlatten args =
        let
          f ABottom = (IntSet.empty, ABottom)
          f (ALam argA argR dir a) = ALam argA argR dir <$> transform (lambdas + 1) a
          args1 = f <$> args
          args2 = snd <$> args1
          used = IntSet.unions $ argumentFlatten $ fmap fst args1

          g ABottom = ABottom
          g (ALam _ _ _ a) = annotationIncrementScope (-1) 0 a
        in
          if lambdas `IntSet.member` used then
            (IntSet.delete lambdas used, AFix FixRegionsNone sorts args2)
          else
            (used, argumentToAnnotation $ g <$> args)
    transform lambdas (AFix fixRegions sorts args) = AFix fixRegions sorts <$> transformArgument lambdas args
    transform lambdas (AForall a) = AForall <$> transform lambdas a
    transform lambdas (ALam argA argR dir a) = (IntSet.delete lambdas used, ALam argA argR dir a')
      where
        (used, a') = transform (lambdas + 1) a
    transform lambdas (AApp a argA argR dir) = (IntSet.union used1 used2, AApp a' argA' argR dir)
      where
        (used1, a') = transform lambdas a
        (used2, argA') = transformArgument lambdas argA
    transform lambdas (AInstantiate a tp) = (`AInstantiate` tp) <$> transform lambdas a
    transform lambdas (ATuple as) = (IntSet.unions used, ATuple as')
      where
        (used, as') = unzip $ map (transform lambdas) as
    transform lambdas (AProject a idx) = (`AProject` idx) <$> transform lambdas a
    transform lambdas (AVar var) = (IntSet.singleton $ lambdas - indexBoundLambda var, AVar var)
    transform lambdas (ARelation cs) = (IntSet.empty, ARelation cs)
    transform lambdas ABottom = (IntSet.empty, ABottom)
    transform lambdas (AJoin a1 a2) = (IntSet.union used1 used2, AJoin a1' a2')
      where
        (used1, a1') = transform lambdas a1
        (used2, a2') = transform lambdas a2
    
    transformArgument :: Int -> Argument Annotation -> (IntSet, Argument Annotation)
    transformArgument lambdas arg = (IntSet.unions $ argumentFlatten $ fmap fst arg', snd <$> arg')
      where
        arg' = transform lambdas <$> arg
