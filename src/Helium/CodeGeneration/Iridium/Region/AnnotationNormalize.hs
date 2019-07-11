module Helium.CodeGeneration.Iridium.Region.AnnotationNormalize (annotationNormalize, annotationArgumentNormalize, annotationIncrementScope, annotationArgumentRemoveUnusedRegionArguments, annotationArgumentCheckSort, sortCompare) where

import Data.List
import Data.Maybe
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
  where
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
    lambdas = case [(argA, argR, a) | ALam argA argR a <- as] of
      [] -> []
      as@((argA, argR, _) : _) -> [ALam argA argR $ annotationJoin $ map (\(_,_,a) -> a) as]
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
      AApp _ _ _ -> True
      AInstantiate _ _ -> True
      _ -> False
annotationNormalize'' env sortEnv (AFix fixRegions s a) = annotationIterate env sortEnv fixRegions s a [] >>= f
  where
    f (_, s, a') = ArgumentValue $ Just (s, [a'])
annotationNormalize'' env sortEnv (AForall a) = argumentAnnotationMap SortForall (const AForall) $ annotationNormalize'' env sortEnv' a
  where
    sortEnv' = sortEnvIncrement sortEnv
annotationNormalize'' env sortEnv (ATuple as) = ArgumentList $ map (annotationNormalize'' env sortEnv) as
annotationNormalize'' env sortEnv (AProject a idx) = case annotationNormalize'' env sortEnv a of
  ArgumentList as -> as !! idx
  ArgumentValue Nothing -> ArgumentValue Nothing
  ArgumentValue a' -> error $ "annotationNormalize: Expected argument list, got " ++ show a'
annotationNormalize'' env sortEnv (ALam argA argR a) = argumentAnnotationMap (SortFun argA argR) (const $ ALam argA argR) $ annotationNormalize'' env sortEnv' a
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
annotationIncrementScope 0 0 = id
annotationIncrementScope incLambda incForall = increment 1 0
  where
    increment :: Int -> Int -> Annotation -> Annotation
    increment minLambda minForall (AFix fixRegions s a) = AFix fixRegions (sortIncreaseScope incForall minForall <$> s) (increment minLambda minForall <$> a)
    increment minLambda minForall (AForall a) = AForall $ increment minLambda (minForall + 1) a
    increment minLambda minForall (ATuple as) = ATuple $ map (increment minLambda minForall) as
    increment minLambda minForall (AProject a idx) = AProject (increment minLambda minForall a) idx
    increment minLambda minForall (ALam annotations regions a) = ALam (sortIncreaseScope incForall minForall <$> annotations) (regionIncreaseScope incForall minForall <$> regions) $ increment (minLambda + 1) minForall a
    increment minLambda minForall (AApp a1 annotations regions) = AApp
      (increment minLambda minForall a1)
      (fmap (increment minLambda minForall) annotations)
      (fmap (variableIncrementLambdaBound minLambda incLambda) regions)
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
    f (higherOrderFixpoint, s', a') = annotationApply env sortEnv (not higherOrderFixpoint) s' a' args
annotationApply env sortEnv _ (SortForall s) (AForall a) (AOIInstantiation tp : args)
  = annotationInstantiate env sortEnv (TypeInstantiation 0 tp) s a >>= (\(s', a') -> annotationApply env sortEnv False s' a' args)
annotationApply env sortEnv _ s1 a1@(ALam _ _ _) args@(AOIApplication _ _ : _)
  | not $ sortCompare (ArgumentValue s1) $ annotationCheckSort env sortEnv [] a1 = error "annotationApplyLambda: input sort error"
  | otherwise = case annotationApplyLambda env sortEnv s1 a1 args [] [] of
  Nothing -> ArgumentValue Nothing
  Just (s2, a2, args')
    | not $ sortCompare (ArgumentValue s2) $ annotationCheckSort env sortEnv [] a2 -> error "annotationApplyLambda: output sort error"
    | otherwise -> annotationApply env sortEnv False s2 a2 args'
annotationApply env sortEnv False s a args = annotationNormalize'' env sortEnv a >>~ (\s' a' -> annotationApply env sortEnv True s' a' args)
annotationApply env sortEnv True s a args = (\(s', a') -> Just (s', [a'])) <$> (annotationAddApplications' env sortEnv s a args)

annotationAddApplications' :: EffectEnvironment -> SortEnv -> Sort -> Annotation -> [ApplicationOrInstantiation] -> Argument (Sort, Annotation)
annotationAddApplications' effectEnv sortEnv (SortForall sort) a (AOIInstantiation tp : args) =
  annotationToArgument (instantiateType effectEnv tp sort) (AInstantiate a tp) >>= (\(s, a') -> annotationAddApplications' effectEnv sortEnv s a' args)
annotationAddApplications' effectEnv sortEnv (SortFun sortA _ sort) a (AOIApplication argA argR : args) = annotationAddApplications' effectEnv sortEnv sort (AApp a argA' argR) args
  where
    argA' = snd <$> annotationArgumentNormalize effectEnv sortEnv sortA argA
annotationAddApplications' effectEnv sortEnv sort a [] = ArgumentValue (sort, a)
annotationAddApplications' _ sortEnv sort  a args = error $ "annotationAddApplications: Illegal arguments: " ++ show (sort, a, args)
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

annotationApplyLambda :: EffectEnvironment -> SortEnv -> Sort -> Annotation -> [ApplicationOrInstantiation] -> [[Annotation]] -> [[RegionVar]] -> Maybe (Sort, Annotation, [ApplicationOrInstantiation])
annotationApplyLambda _ _ _ ABottom _ _ _ = Nothing
annotationApplyLambda env sortEnv (SortFun sortAnnotation' _ s) (ALam sortAnnotation sortRegion a) (AOIApplication argA argR : args) aSubst rSubst
  | sortAnnotation' /= sortAnnotation = error $ "Sort mismatch: " ++ show sortAnnotation' ++ " & " ++ show sortRegion
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
    substitute firstLambda forallNesting x@(ALam argAnnotation argRegion a) =
      ALam argAnnotation argRegion $ substitute (firstLambda + 1) forallNesting a
    substitute firstLambda forallNesting (AApp a argA argR) =
      AApp
        (substitute firstLambda forallNesting a)
        (fmap (substitute firstLambda forallNesting) argA)
        (fmap (substituteRegionVar firstLambda) argR)
    substitute firstLambda forallNesting (AInstantiate a tp) = AInstantiate (substitute firstLambda forallNesting a) tp
    substitute firstLambda forallNesting (AVar var)
      | lambdaIndex < firstLambda = AVar var
      | lambdaIndex >= firstLambda + count = AVar $ variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = annotationIncrementScope (firstLambda - 1) forallNesting $ (substitutionAnnotation !!! (count - lambdaIndex + firstLambda - 1)) !!! argumentIndex
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
annotationInstantiate' env sortEnv inst args (AProject _ _) = error "annotationInstantiate': Did not expect an extract here"
annotationInstantiate' env sortEnv inst args (ALam argA argR a) = fmap f <$> annotationInstantiate' env sortEnv' inst args' a
  where
    f (s, a') = (SortFun argA' argR' s, ALam argA' argR' a')

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
annotationInstantiate' env sortEnv inst args (AApp a argA argR) = fmap f <$> annotationInstantiate' env sortEnv inst args a
  where
    f (SortFun sortA sortR s, a') = (s, AApp a' (fmap snd argA') argR')
      where
        argA' = annotationArgumentInstantiate env sortEnv inst args (zipArgument (\s a -> (s, a)) sortA argA)
        argR' = argR >>= lookupRegionVar
    lookupRegionVar var = case tryIndex args $ indexBoundLambda var - 1 of
      Just (_, regions) -> fmap (variableFromIndices $ indexBoundLambda var) $ regions !!! indexInArgument var
      Nothing -> ArgumentValue var
annotationInstantiate' env sortEnv inst args (AInstantiate a tp) = (>>= f) <$> annotationInstantiate' env sortEnv inst args a
  where
    tp' = tpInstantiate' inst tp

    f :: (Sort, Annotation) -> Argument (Sort, Annotation)
    f (SortForall s, AForall a') = annotationInstantiate env sortEnv (TypeInstantiation 0 tp') s a'
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
    f (sort, annotation) = case annotationInstantiate' env sortEnv inst args annotation of
      Just annotations -> annotations
      Nothing -> (\s -> (s, ABottom)) <$> instantiateType' env inst sort

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
gatherApplications (AApp a argA argR) args = gatherApplications a (AOIApplication argA argR : args)
gatherApplications a args = (a, args)

data ApplicationOrInstantiation
  = AOIApplication !(Argument Annotation) !(Argument RegionVar)
  | AOIInstantiation !Tp
  
instance Show ApplicationOrInstantiation where
  show (AOIApplication argA argR) = "[" ++ show argA ++ "; " ++ show argR ++ "]"
  show (AOIInstantiation tp) = "{ " ++ show tp ++ " }"

aoiMapAnnotation :: (Annotation -> Annotation) -> ApplicationOrInstantiation -> ApplicationOrInstantiation
aoiMapAnnotation f (AOIApplication a r) = AOIApplication (fmap f a) r
aoiMapAnnotation _ (AOIInstantiation tp) = AOIInstantiation tp

aoiFlattenAnnotations :: ApplicationOrInstantiation -> [Annotation]
aoiFlattenAnnotations (AOIApplication a _) = argumentFlatten a
aoiFlattenAnnotations _ = []

-- Iterates a saturated fixpoint annotation of the form `(fix(_regions) (psi_1) psi_2) [\hat{\psi}; \hat{\rho}] ..`, of kind *.
-- Bool in return type denotes whether the result is a higher order fixpoint
annotationIterate :: EffectEnvironment -> SortEnv -> FixRegions -> Argument Sort -> Argument Annotation -> [ApplicationOrInstantiation] -> Argument (Bool, Sort, Annotation)
annotationIterate _ _ _ _ (ArgumentList []) _ = ArgumentList []
annotationIterate env sortEnv fixRegions sorts initial application = zipArgument (\s (h, a) -> (h, s, a)) sorts $ iterate 0 initial
  where
    bottom = ABottom <$ sorts

    sortsTest = SortFun sorts argumentEmpty <$> sorts

    recursiveArgument = AVar <$> sortArgumentToArgument 1 sorts
    sortEnvBody = argumentFlatten sorts : sortEnv

    -- TODO: Escape check

    iterate :: Int -> Argument Annotation -> Argument (Bool, Annotation)
    iterate 4 _ = error "annotationIterate: probably infinite recursion"
    iterate iteration current
      | not $ sortCompare sortsTest $ annotationArgumentCheckSort env sortEnv [] current = error $ "iterate: current not correct\n" ++ show sortsTest ++ "\n" ++ show (annotationArgumentCheckSort env sortEnv [] current)
      | not $ sortCompare sortsTest $ annotationArgumentCheckSort env sortEnv [] next = error $ "iterate: next not correct"
      | otherwise = 
      case isFixed current next of
        HigherOrderFixpoint -> fmap (\a -> (True, a)) $ bindWithSort (applyWith sortEnv bottom) sorts current
        FirstOrderFixpoint -> undefined -- TODO: Rewrite to element-wise fixpoint
        NoFixpoint
          | sortCompare (SortFun sorts argumentEmpty <$> sorts) $ annotationArgumentCheckSort env sortEnv [] next
              -> iterate (iteration + 1) next
          | otherwise -> error "sort error in iteration"
      where
        next = bindWithSort (iterateNext current) sorts current

    isFixed :: Argument Annotation -> Argument Annotation -> FixpointState
    isFixed arg1 arg2
      | arg1' == arg2' = HigherOrderFixpoint
      -- TODO: First order fixpoint
      | otherwise = NoFixpoint
      where
        arg1' = bindWithSort (applyWith sortEnv bottom) sorts arg1
        arg2' = bindWithSort (applyWith sortEnv bottom) sorts arg2

    iterateNext :: Argument Annotation -> Argument Sort -> Annotation -> Argument Annotation
    iterateNext with s a
      = ALam sorts argumentEmpty <$> applyWith sortEnvBody with' s (annotationIncrementScope 1 0 a)
      where
        with' = (\a' -> AApp (annotationIncrementScope 1 0 a') recursiveArgument argumentEmpty) <$> with

    applyWith :: SortEnv -> Argument Annotation -> Argument Sort -> Annotation -> Argument Annotation
    applyWith sortEnv' with s a = annotationNormalize env sortEnv' s $ AApp a with argumentEmpty

data FixpointState = NoFixpoint | FirstOrderFixpoint | HigherOrderFixpoint

annotationApplicationHasUnboundAnnotationVar :: Int -> [ApplicationOrInstantiation] -> Bool
annotationApplicationHasUnboundAnnotationVar scope application = any (annotationHasUnboundAnnotationVar False scope) (application >>= aoiFlattenAnnotations)

-- Checks whether an annotation has unbound annotation variable
annotationHasUnboundAnnotationVar :: Bool -> Int -> Annotation -> Bool
annotationHasUnboundAnnotationVar exact minScope (AFix _ _ arg) = any (annotationHasUnboundAnnotationVar exact minScope) $ argumentFlatten arg
annotationHasUnboundAnnotationVar exact minScope (AForall a) = annotationHasUnboundAnnotationVar exact minScope a
annotationHasUnboundAnnotationVar exact minScope (ATuple as) = any (annotationHasUnboundAnnotationVar exact minScope) as
annotationHasUnboundAnnotationVar exact minScope (AProject a idx) = annotationHasUnboundAnnotationVar exact minScope a
annotationHasUnboundAnnotationVar exact minScope (ALam _ _ a) = annotationHasUnboundAnnotationVar exact (minScope + 1) a
annotationHasUnboundAnnotationVar exact minScope (AApp a argA argR)
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

{-
-- Substitutes all free variables with bottom
-- Assumes that all fixpoints are in a first order fixpoint
annotationToFirstOrder :: HandleFixpointArgument -> Int -> Annotation -> Annotation
annotationToFirstOrder fixpointArgument@(HandleFixpointArgumentIterateNested fixpointScope) minScope (AFix fixRegions sort (ArgumentValue a))
  | annotationHasUnboundAnnotationVar True fixpointScope a = case fixRegions of
    FixRegionsNone -> AApp
      (annotationToFirstOrder fixpointArgument minScope a)
      (ArgumentValue $ annotationToFirstOrder fixpointArgument minScope a1)
      argumentEmpty
    FixRegionsEscape arity sort ->
      let
        argRegion = sortArgumentToArgument 1 sort
      in
        annotationToFirstOrder fixpointArgument minScope $ ALam argumentEmpty sort $ AApp (annotationIncrementScope 1 0 a2) (ArgumentValue $ annotationIncrementScope 1 0 a1) argRegion
annotationToFirstOrder fixpointArgument minScope (AFix _ fixRegions a1 a2)
  = annotationToFirstOrder fixpointArgument minScope a1
annotationToFirstOrder fixpointArgument minScope (AForall a)
  = AForall $ annotationToFirstOrder fixpointArgument minScope a
annotationToFirstOrder fixpointArgument minScope (ALam argAnnotation argRegion a)
  = ALam argAnnotation argRegion $ annotationToFirstOrder (handleFixpointArgumentIncrement fixpointArgument) (minScope + 1) a
annotationToFirstOrder fixpointArgument minScope (AApp a argAnnotation argRegion) = AApp
  (annotationToFirstOrder fixpointArgument minScope a)
  (fmap (annotationToFirstOrder fixpointArgument minScope) argAnnotation)
  argRegion
annotationToFirstOrder fixpointArgument minScope (AInstantiate a tp)
  = AInstantiate (annotationToFirstOrder fixpointArgument minScope a) tp
annotationToFirstOrder (HandleFixpointArgumentSubstitutute scope incLambda incForall a) _ (AVar var)
  | indexBoundLambda var == scope = annotationIncrementScope incLambda incForall a
annotationToFirstOrder fixpointArgument minScope (AVar var)
  | indexBoundLambda var >= minScope = ABottom
  | otherwise = AVar var
annotationToFirstOrder fixpointArgument minScope (AJoin a1 a2)
  = AJoin (annotationToFirstOrder fixpointArgument minScope a1) (annotationToFirstOrder fixpointArgument minScope a2)
annotationToFirstOrder _ _ a = a

-- Describes how the argument of a fixpoint should be handled
data HandleFixpointArgument 
  = HandleFixpointArgumentNone
  | HandleFixpointArgumentIterateNested !Int -- Apply one iteration for nested fixpoints
  | HandleFixpointArgumentSubstitutute !Int !Int !Int !Annotation

handleFixpointArgumentIncrement :: HandleFixpointArgument -> HandleFixpointArgument
handleFixpointArgumentIncrement HandleFixpointArgumentNone = HandleFixpointArgumentNone
handleFixpointArgumentIncrement (HandleFixpointArgumentIterateNested idx) = HandleFixpointArgumentIterateNested $ idx + 1
handleFixpointArgumentIncrement (HandleFixpointArgumentSubstitutute idx increment incrementForall a) = HandleFixpointArgumentSubstitutute (idx + 1) (increment + 1) incrementForall a
-}

annotationArgumentRemoveUnusedRegionArguments :: Argument Annotation -> ([Maybe Int], Argument Annotation)
annotationArgumentRemoveUnusedRegionArguments arguments@(ArgumentList []) = ([], arguments)
annotationArgumentRemoveUnusedRegionArguments arguments = (mapping, fmap substitute arguments)
  where
    used = IntSet.unions $ map annotationUsedRegionVariables $ argumentFlatten arguments

    regions = case filter (ABottom /=) $ argumentFlatten arguments of
      ALam _ (ArgumentList regions) _ : _ -> regions
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

    substitution = map (maybe regionGlobal (variableFromIndices 1)) mapping
    substitute (ALam (ArgumentList []) _ a) = ALam
      (ArgumentList [])
      (ArgumentList $ replicate regionCount $ ArgumentValue SortArgumentRegionMonomorphic)
      $ annotationSubstitute' [[]] [substitution] 2 0 $ annotationIncrementScope 1 0 a
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
    addForallsLambdas lambdas foralls (SortFun sortA sortR s) = ALam sortA sortR $ addForallsLambdas (lambdas + 1) foralls s
    addForallsLambdas lambdas foralls _ = applications lambdas foralls annotationSort (annotationIncrementScope lambdas foralls annotation)

    applications :: Int -> Int -> Sort -> Annotation -> Annotation
    applications lambdas foralls (SortForall s) a = applications lambdas (foralls - 1) s $ AInstantiate a (TpVar $ TypeVar $ foralls - 1)
    applications lambdas foralls (SortFun sortA sortR s) a = applications (lambdas - 1) foralls s $ AApp a (AVar <$> sortArgumentToArgument lambdas sortA) (sortArgumentToArgument lambdas sortR)
    applications 0 0 _ a = a
    applications _ _ _ _ = error "annotationSaturateWithSort: error in lambda and forall count"

annotationArgumentCheckSort :: EffectEnvironment -> SortEnv -> RegionEnv -> Argument Annotation -> Argument (Maybe Sort)
annotationArgumentCheckSort env sortEnv regionEnv arg = arg >>= annotationCheckSort env sortEnv regionEnv

type RegionEnv = [[SortArgumentRegion]]
regionEnvIncrement = fmap $ fmap f
  where
    f SortArgumentRegionMonomorphic = SortArgumentRegionMonomorphic
    f (SortArgumentRegionPolymorphic (TypeVar idx) tps) = SortArgumentRegionPolymorphic (TypeVar $ idx + 1) (tpIncreaseScope 1 0 <$> tps)

annotationCheckSort' :: EffectEnvironment -> SortEnv -> RegionEnv -> Annotation -> Argument (Maybe Sort)
annotationCheckSort' env sortEnv regionEnv a = annotationCheckSort env sortEnv regionEnv a

annotationCheckSort :: EffectEnvironment -> SortEnv -> RegionEnv -> Annotation -> Argument (Maybe Sort)
annotationCheckSort env sortEnv regionEnv (AFix _ sort args)
  | sortCompare (SortFun sort argumentEmpty <$> sort) sortBody = Just <$> sort
  | otherwise = error $ "Sort of fix combinator does not match body.\nFix: " ++ show sort ++ "\nBody: " ++ show sortBody
  where
    sortBody = annotationArgumentCheckSort env sortEnv regionEnv args
annotationCheckSort env sortEnv regionEnv (AForall a) = fmap SortForall <$> annotationCheckSort env (sortEnvIncrement sortEnv) (regionEnvIncrement regionEnv) a
annotationCheckSort env sortEnv regionEnv (ALam argA argR a) = fmap (SortFun argA argR) <$> annotationCheckSort env sortEnv' regionEnv' a
  where
    sortEnv' = argumentFlatten argA : sortEnv
    regionEnv' = argumentFlatten argR : regionEnv
annotationCheckSort env sortEnv regionEnv (AApp a argA argR) = fmap f <$> annotationCheckSort env sortEnv regionEnv a
  where
    f (SortFun sortA sortR s)
      | not $ sortCompare sortA argSort = error $ "Sort of argument in application does not match.\nFunction sort: " ++ show sortA ++ "\nArgument sort: " ++ show argSort
      | not $ regionArgumentCompare (show (length sortEnv, length regionEnv)) regionEnv sortR argR = error $ "Sort of region argument in application does not match.\nFunction sort: " ++ show sortR ++ "\nArgument: " ++ show argR ++ "\nRegion env: " ++ show regionEnv ++ "\n" ++ show (length sortEnv, length regionEnv)
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
  | otherwise = error $ "Relation has undeclared region variables: " ++ show cs ++ "\n" ++ show regionEnv ++ "\n" ++ show (filter (not . exist2) cs)
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

regionArgumentCompare :: String -> RegionEnv -> Argument SortArgumentRegion -> Argument RegionVar -> Bool
regionArgumentCompare str env (ArgumentValue s1) (ArgumentValue var) = case regionEnvLookup str env var of
  Just s2
    | s1 == s2 -> True
    | otherwise -> case (s1, s2) of
      (SortArgumentRegionPolymorphic _ _, SortArgumentRegionMonomorphic) -> True
      _ -> False
  Nothing -> True
regionArgumentCompare str env (ArgumentList _) (ArgumentValue var) = case regionEnvLookup str env var of
  Just s2 -> s2 == SortArgumentRegionMonomorphic
  Nothing -> True
regionArgumentCompare str env (ArgumentList sorts) (ArgumentList rs) =
  length sorts == length rs && all (uncurry $ regionArgumentCompare str env) (zip sorts rs)
regionArgumentCompare _ _ _ _ = False

regionEnvLookup :: String -> RegionEnv -> RegionVar -> Maybe SortArgumentRegion
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
sortCompare' s1 s2 = error $ "Wrong\n" ++ show s1 ++ "\n" ++ show s2 -- _ _ = False

sortCompare :: Argument Sort -> Argument (Maybe Sort) -> Bool
sortCompare = sortCompare' . fmap Just

sortJoin :: Argument (Maybe Sort) -> Argument (Maybe Sort) -> Argument (Maybe Sort)
sortJoin (ArgumentList as) (ArgumentList bs) = ArgumentList $ uncurry sortJoin <$> zip as bs
sortJoin (ArgumentValue (Just s1)) _ = ArgumentValue $ Just s1
sortJoin _ (ArgumentValue (Just s2)) = ArgumentValue $ Just s2
sortJoin _ _ = ArgumentValue Nothing

annotationEscapeCheck :: Int -> Argument Annotation -> (IntMap Int, IntSet)
annotationEscapeCheck arity arguments
  where
    argumentMain : argumentsRest = drop (arity - 1) $ argumentFlatten arguments
