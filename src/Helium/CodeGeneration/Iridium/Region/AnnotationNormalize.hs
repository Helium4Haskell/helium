module Helium.CodeGeneration.Iridium.Region.AnnotationNormalize (annotationNormalize, annotationIncrementScope, annotationArgumentRemoveUnusedRegionArguments, annotationSaturate, annotationSaturateWithSort) where

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

annotationNormalize :: EffectEnvironment -> Annotation -> Annotation
annotationNormalize env a = snd $ annotationNormalize' env $ snd $ annotationUniqueFixpoints 0 a

-- Assign a unique number to each fixpoint. Used for identifying fixpoints in nested fixpoint iterations.
annotationUniqueFixpoints :: Int -> Annotation -> (Int, Annotation)
annotationUniqueFixpoints fresh (AFix _ fixRegions a1 a2) = (fresh + 1, AFix (Just fresh) fixRegions a1 a2)
annotationUniqueFixpoints fresh (AForall a) = AForall <$> annotationUniqueFixpoints fresh a
annotationUniqueFixpoints fresh (ALam argA argR a) = ALam argA argR <$> annotationUniqueFixpoints fresh a
annotationUniqueFixpoints fresh (AApp a argA argR) = (fresh'', AApp a' argA' argR)
  where
    (fresh', a') = annotationUniqueFixpoints fresh a
    (fresh'', argA') = mapAccumL annotationUniqueFixpoints fresh' argA
annotationUniqueFixpoints fresh (AInstantiate a tp) = (`AInstantiate` tp) <$> annotationUniqueFixpoints fresh a
annotationUniqueFixpoints fresh (AJoin a1 a2) = (fresh'', AJoin a1' a2')
  where
    (fresh', a1') = annotationUniqueFixpoints fresh a1
    (fresh'', a2') = annotationUniqueFixpoints fresh a2
annotationUniqueFixpoints fresh a = (fresh, a) -- AVar, ARelation, ABottom

annotationNormalize' :: EffectEnvironment -> Annotation -> FixpointInfo Annotation
annotationNormalize' env a = annotationJoin <$> annotationNormalize'' env a

annotationJoin :: [Annotation] -> Annotation
annotationJoin [] = ABottom
annotationJoin [a] = a
annotationJoin as = foldr1 AJoin $ annotationGroup as

annotationJoinUnsorted :: [Annotation] -> Annotation
annotationJoinUnsorted [] = ABottom
annotationJoinUnsorted as = foldr1 AJoin as

annotationGroup :: [Annotation] -> [Annotation]
annotationGroup as =
  nubSort [a | a@(AFix _ _ _ _) <- as]
  ++ foralls
  ++ lambdas
  ++ nubSort [a | a@(AApp _ _ _) <- as]
  ++ nubSort [a | a@(AInstantiate _ _) <- as]
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

type FixpointInfo a = ([(Int, Annotation)], a)

annotationNormalize'' :: EffectEnvironment -> Annotation -> FixpointInfo [Annotation]
annotationNormalize'' env a
  | isAppLike = annotationApply env a' args
  where
    (a', args) = gatherApplications a []
    isAppLike = case a of
      AApp _ _ _ -> True
      AInstantiate _ _ -> True
      AFix _ _ _ _ -> True
      _ -> False
annotationNormalize'' env (AForall a) = map AForall <$> annotationNormalize'' env a
annotationNormalize'' env (ALam argA argR a) = map (ALam argA argR) <$> annotationNormalize'' env a
annotationNormalize'' env ABottom = ([], [])
annotationNormalize'' env (AJoin a1 a2) = (info1 ++ info2, as1 ++ as2)
  where
    (info1, as1) = annotationNormalize'' env a1
    (info2, as2) = annotationNormalize'' env a2
annotationNormalize'' env a = ([], [a])

annotationIncrementScope :: Int -> Int -> Annotation -> Annotation
annotationIncrementScope 0 0 = id
annotationIncrementScope incLambda incForall = increment 1 0
  where
    increment :: Int -> Int -> Annotation -> Annotation
    increment minLambda minForall (AFix _ fixRegions a1 a2) = AFix Nothing fixRegions (increment minLambda minForall a1) (increment minLambda minForall a2)
    increment minLambda minForall (AForall a) = AForall $ increment minLambda (minForall + 1) a
    increment minLambda minForall (ALam annotations regions a) = ALam annotations regions $ increment (minLambda + 1) minForall a
    increment minLambda minForall (AApp a1 annotations regions) = AApp
      (increment minLambda minForall a1)
      (fmap (increment minLambda minForall) annotations)
      (fmap (variableIncrementLambdaBound minLambda incLambda) regions)
    increment minLambda minForall (AVar avar) = AVar $ variableIncrementLambdaBound minLambda incLambda avar
    increment minLambda minForall (ARelation constraints) =
      ARelation $ map (\(Outlives r1 r2) -> Outlives (variableIncrementLambdaBound minLambda incLambda r1) (variableIncrementLambdaBound minLambda incLambda r2)) constraints
    increment minLambda minForall ABottom = ABottom
    increment minLambda minForall (AJoin a1 a2) = AJoin (increment minLambda minForall a1) (increment minLambda minForall a2)

gatherApplications' :: Annotation -> (Annotation, [Argument Annotation], [Argument RegionVar])
gatherApplications' (AApp a argA argR) = (a', argA : annotations, argR : regions)
  where
    (a', annotations, regions) = gatherApplications' a
gatherApplications' a = (a, [], [])

data Substitution = Substitution
  { substitutionFirst :: !Int
  , substitutionCount :: !Int
  , substitutionAnnotations :: ![[Annotation]]
  , substitutionRegions :: ![[RegionVar]]
  , substitutionForallNesting :: !Int
  }

annotationApply :: EffectEnvironment -> Annotation -> [ApplicationOrInstantiation] -> FixpointInfo [Annotation]
annotationApply env ABottom _ = ([], [])
annotationApply env a [] = ([], [a])
annotationApply env (AJoin a1 a2) args = (info1 ++ info2, as1 ++ as2)
  where
    (info1, as1) = annotationApply env a1 args
    (info2, as2) = annotationApply env a2 args
annotationApply env (AFix identifier fixRegions lower body) args =
  ( infoSelf ++ info
  , as
  )
  where
    infoSelf = case identifier of
      Nothing -> []
      Just idx -> [(idx, AFix identifier fixRegions lowerBound body')]
    (body', a) = annotationIterate env identifier fixRegions lower body args
    (isHigherOrderFixpoint, lowerBound) = case a of
      AFix _ _ lb _ -> (False, lb)
      _ -> (True, a)
    (info, as)
      | isHigherOrderFixpoint = annotationApply env a args
      | otherwise = ([], [annotationAddApplications a args])
annotationApply env (AForall a) (AOIInstantiation tp : args) = annotationApply env (annotationInstantiate env (TypeVar 0) tp a) args
annotationApply env a allArgs@(AOIInstantiation tp : args) = case a1 of
  AForall a2 -> (info, [annotationInstantiate env (TypeVar 0) tp a2])
  _ -> (info, [AInstantiate a1 tp])
  where
    (info, a1) = annotationNormalize' env a
annotationApply env a1 args@(AOIApplication _ _ : _) = case annotationApplyLambda a1 args [] [] of
  (a2, []) -> ([], [a2]) -- All arguments are processed
  (a2, args'@(AOIApplication _ _ : _)) ->
    let
      (info1, as3) = annotationNormalize'' env a2
      (infos2, ass4) = unzip $ map (\a -> if canEval a then annotationApply env a args' else ([], [annotationAddApplications a args'])) as3
    in
      (info1 ++ concat infos2, concat ass4)
  (a2, args') -> annotationApply env a2 args'
  where
    canEval a = case a of
      ALam _ _ _ -> True
      AJoin _ _ -> True
      AFix _ _ _ _ -> True
      _ -> False

annotationAddApplications :: Annotation -> [ApplicationOrInstantiation] -> Annotation
annotationAddApplications a (AOIInstantiation tp : args) = annotationAddApplications (AInstantiate a tp) args
annotationAddApplications a (AOIApplication argA argR : args) = annotationAddApplications (AApp a argA argR) args
annotationAddApplications a [] = a
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
annotationArgumentMapping :: SortArgument SortArgumentRegion -> Argument RegionVar -> [RegionVar]
annotationArgumentMapping sortArg (ArgumentValue b) = b <$ sortArgumentFlatten sortArg
annotationArgumentMapping (SortArgumentList as) (ArgumentList bs) = concat $ zipWith annotationArgumentMapping as bs

annotationApplyLambda :: Annotation -> [ApplicationOrInstantiation] -> [[Annotation]] -> [[RegionVar]] -> (Annotation, [ApplicationOrInstantiation])
annotationApplyLambda ABottom _ _ _ = (ABottom, [])
annotationApplyLambda (ALam _ sortRegion a) (AOIApplication argA argR : args) aSubst rSubst
  = annotationApplyLambda a args (argumentFlatten argA : aSubst) (annotationArgumentMapping sortRegion argR : rSubst)
annotationApplyLambda a args [] [] = (a, args)
annotationApplyLambda a args aSubst rSubst
  = (annotationSubstitute aSubst rSubst a, args)

annotationSubstitute :: [[Annotation]] -> [[RegionVar]] -> Annotation -> Annotation
annotationSubstitute substitutionAnnotation substitutionRegion = annotationSubstitute' substitutionAnnotation substitutionRegion 1 0

annotationSubstitute' :: [[Annotation]] -> [[RegionVar]] -> Int -> Int -> Annotation -> Annotation
annotationSubstitute' substitutionAnnotation substitutionRegion = substitute
  where
    count = length substitutionAnnotation -- should be equal to `length substitutionRegion`

    substitute :: Int -> Int -> Annotation -> Annotation
    substitute firstLambda forallNesting (AFix _ fixRegions a1 a2) = AFix Nothing fixRegions (substitute firstLambda forallNesting a1) (substitute firstLambda forallNesting a2)
    substitute firstLambda forallNesting (AForall a) = AForall $ substitute firstLambda (forallNesting + 1) a
    substitute firstLambda forallNesting (ALam argAnnotation argRegion a) =
      ALam argAnnotation argRegion $ substitute (firstLambda + 1) forallNesting a
    substitute firstLambda forallNesting (AApp a argA argR) = AApp a (fmap (substitute firstLambda forallNesting) argA) (fmap (substituteRegionVar firstLambda) argR)
    substitute firstLambda forallNesting (AInstantiate a tp) = AInstantiate (substitute firstLambda forallNesting a) tp
    substitute firstLambda forallNesting (AVar var)
      | lambdaIndex < firstLambda = AVar var
      | lambdaIndex > firstLambda + count = AVar $ variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = annotationIncrementScope (firstLambda - 1) forallNesting $ (substitutionAnnotation !!! (lambdaIndex - firstLambda)) !!! argumentIndex
      where
        lambdaIndex = indexBoundLambda var
        argumentIndex = indexInArgument var
    substitute firstLambda forallNesting (ARelation cs)
      | null cs = ABottom
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
      | lambdaIndex > firstLambda + count = variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = variableIncrementLambdaBound 1 (lambdaIndex - 1) $ (substitutionRegion !!! (lambdaIndex - firstLambda)) !!! argumentIndex
      where
        lambdaIndex = indexBoundLambda var
        argumentIndex = indexInArgument var

annotationInstantiate :: EffectEnvironment -> TypeVar -> Tp -> Annotation -> Annotation
annotationInstantiate env tvar tp a = annotationInstantiate' env tvar tp [] [] a

annotationInstantiate' :: EffectEnvironment -> TypeVar -> Tp -> [[Argument Int]] -> [[Argument Int]] -> Annotation -> Annotation
annotationInstantiate' env tvar tp aSubst rSubst (AFix fixIdentifier fixRegions a1 a2)
  = AFix fixIdentifier fixRegions
    (annotationInstantiate' env tvar tp aSubst rSubst a1)
    (annotationInstantiate' env tvar tp aSubst rSubst a2)
annotationInstantiate' env (TypeVar tvar) tp aSubst rSubst (AForall a)
  = annotationInstantiate' env (TypeVar $ tvar + 1) tp aSubst rSubst a
annotationInstantiate' env tvar tp aSubst rSubst (ALam argA argR a)
  = ALam argA argR $ annotationInstantiate' env tvar tp (argAnnotationSubst : aSubst) (argRegionSubst : rSubst) a
  where
    argAnnotationSubst = snd $ annotationInstantiationSubstitution (typeAnnotationSortArgument env tp) tvar 0 argA
    argRegionSubst = snd $ annotationInstantiationSubstitution (typeRegionChildSort env tp) tvar 0 argR
annotationInstantiate' env tvar tp aSubst rSubst (AApp a argA argR) = AApp a' argA' argR'
  where
    a' = annotationInstantiate' env tvar tp aSubst rSubst a
    argA' = annotationInstantiate' env tvar tp aSubst rSubst <$> argA
    argR' = argR >>= annotationInstantiateVariable rSubst
annotationInstantiate' env tvar tp aSubst rSubst (AInstantiate a instTp)
  = AInstantiate (annotationInstantiate' env tvar tp aSubst rSubst a) instTp
annotationInstantiate' env tvar tp aSubst rSubst (AVar var) = case annotationInstantiateVariable aSubst var of
  ArgumentValue var' -> AVar var'
  _ -> error "annotationInstantiate: Illegal use of polymorphic argument"
annotationInstantiate' env tvar tp aSubst rSubst (ARelation constraints) = ARelation constraints'
  where
    constraints' = [Outlives r1' r2' | Outlives r1 r2 <- constraints, r1' <- argumentFlatten $ annotationInstantiateVariable rSubst r1, r2' <- argumentFlatten $ annotationInstantiateVariable rSubst r2]
annotationInstantiate' env tvar tp aSubst rSubst ABottom = ABottom
annotationInstantiate' env tvar tp aSubst rSubst (AJoin a1 a2)
  = annotationInstantiate' env tvar tp aSubst rSubst a1
  `AJoin` annotationInstantiate' env tvar tp aSubst rSubst a2

annotationInstantiateVariable :: IndexVariable var => [[Argument Int]] -> var -> Argument var
annotationInstantiateVariable subst var = case tryIndex subst lambda of
  Nothing -> ArgumentValue var
  Just lambdaSubst -> fmap (variableFromIndices lambda) $ lambdaSubst !!! indexInArgument var
  where
    lambda = indexBoundLambda var

annotationInstantiationSubstitution :: ([Tp] -> SortArgument a) -> TypeVar -> Int -> SortArgument a -> (Int, [Argument Int])
annotationInstantiationSubstitution getArgs tvar = substitution
  where
    substitution next (SortArgumentMonomorphic _) = (next + 1, [ArgumentValue next])
    substitution next (SortArgumentPolymorphic tvar' tps)
      | tvar == tvar' = fmap return $ indexSortArgument next $ getArgs tps
      | otherwise = (next + 1, [ArgumentValue next])
    substitution next (SortArgumentList args) = fmap concat $ mapAccumL substitution next args

indexSortArgument :: Int -> SortArgument a -> (Int, Argument Int)
indexSortArgument next (SortArgumentMonomorphic _) = (next + 1, ArgumentValue next)
indexSortArgument next (SortArgumentPolymorphic _ _) = (next + 1, ArgumentValue next)
indexSortArgument next (SortArgumentList args) = fmap ArgumentList $ mapAccumL indexSortArgument next args

-- Returns a list of annotations representing (multivariate) applications (or instantiations)
-- The target of the application is psi_1_0
annotationFindApplications :: Annotation -> [(Int, Int, [ApplicationOrInstantiation])]
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

gatherApplications :: Annotation -> [ApplicationOrInstantiation] -> (Annotation, [ApplicationOrInstantiation])
gatherApplications (AInstantiate a tp) args = gatherApplications a (AOIInstantiation tp : args)
gatherApplications (AApp a argA argR) args = gatherApplications a (AOIApplication argA argR : args)
gatherApplications a args = (a, args)

data ApplicationOrInstantiation
  = AOIApplication !(Argument Annotation) !(Argument RegionVar)
  | AOIInstantiation !Tp

aoiMapAnnotation :: (Annotation -> Annotation) -> ApplicationOrInstantiation -> ApplicationOrInstantiation
aoiMapAnnotation f (AOIApplication a r) = AOIApplication (fmap f a) r
aoiMapAnnotation _ (AOIInstantiation tp) = AOIInstantiation tp

aoiFlattenAnnotations :: ApplicationOrInstantiation -> [Annotation]
aoiFlattenAnnotations (AOIApplication a _) = argumentFlatten a
aoiFlattenAnnotations _ = []

-- Iterates a saturated fixpoint annotation of the form `(fix(_regions) (psi_1) psi_2) [\hat{\psi}; \hat{\rho}] ..`, of kind *.
annotationIterate :: EffectEnvironment -> Maybe Int -> FixRegions -> Annotation -> Annotation -> [ApplicationOrInstantiation] -> (Annotation, Annotation)
annotationIterate env identifier fixRegions lowerBound aOriginal@(ALam argA argR function) mainApplication = (AFix identifier fixRegions annotationFinal $ lam functionFinal, annotationFinal)
  where
    (functionFinal, annotationFinal) = iterate (annotationNormalize env function) (annotationNormalize env lowerBound)

    mainApplication' = map (aoiMapAnnotation (annotationToFirstOrder HandleFixpointArgumentNone 1)) mainApplication
    mainApplicationHasUnbound = annotationApplicationHasUnboundAnnotationVar 1 mainApplication

    lam = ALam argA argR

    iterate :: Annotation -> Annotation -> (Annotation, Annotation)
    iterate function' current = case isFixed function' current next' of
      FirstOrderFixpoint -> (function'', AFix identifier fixRegions next' $ lam function'')
      HigherOrderFixpoint -> (function'', current)
      NoFixpoint -> iterate function'' next'
      where
        application = case fixRegions of
          FixRegionsNone -> AApp (lam function') (ArgumentValue current) (ArgumentList [])
          FixRegionsEscape _ sort ->
            AApp (lam $ annotationIncrementScope 1 0 function') (ArgumentValue $ annotationIncrementScope 1 0 current) (sortArgumentToArgument 0 sort)
        (info, next) = annotationNormalize' env application
        next' = case fixRegions of
          FixRegionsNone -> next
          FixRegionsEscape arity sort ->
            ALam (SortArgumentList []) sort
            $ annotationFilterInternalRegions arity next
        function'' = annotationUpdateLowerbounds info function'

    isFixed :: Annotation -> Annotation -> Annotation -> FixpointState
    isFixed function' previous current
      | previous == current = HigherOrderFixpoint
      | {- all undefined undefined -} False -- TODO: If all applications are fixed
        = if hasUnbound then FirstOrderFixpoint else HigherOrderFixpoint
      | otherwise = NoFixpoint
      where
        equal :: Int -> Int -> [ApplicationOrInstantiation] -> [ApplicationOrInstantiation] -> Bool
        equal lambdas foralls args1 args2 = annotationNormalize env (annotationJoinUnsorted as1) == annotationNormalize env (annotationJoinUnsorted as2)
          where
            (_, as1) = annotationApply env (annotationIncrementScope lambdas foralls previous) args1
            (_, as2) = annotationApply env (annotationIncrementScope lambdas foralls current) args2

        applicationEqual = equal 0 0 mainApplication' mainApplication'

        bodyApplicationEqual :: (Int, Int, [ApplicationOrInstantiation]) -> Bool
        bodyApplicationEqual (lambdas, foralls, application) = equal lambdas foralls app1 app2
          where
            app1 = substituteInApplication previous lambdas foralls application
            app2 = substituteInApplication current lambdas foralls application

        hasUnbound = mainApplicationHasUnbound || any (\(_, _, args) -> annotationApplicationHasUnboundAnnotationVar 2 args) bodyApplications
        -- Note that the applications in the body might change because of nested fixpoints.
        bodyApplications = snd (annotationNormalize'' env (annotationToFirstOrder (HandleFixpointArgumentIterateNested 1) 2 function')) >>= annotationFindApplications

        substituteInApplication :: Annotation -> Int -> Int -> [ApplicationOrInstantiation] -> [ApplicationOrInstantiation]
        substituteInApplication a lambdas foralls application
          = map
            (aoiMapAnnotation (annotationToFirstOrder (HandleFixpointArgumentSubstitutute (lambdas + 1) lambdas foralls a) 1))
            application

data FixpointState = NoFixpoint | FirstOrderFixpoint | HigherOrderFixpoint

annotationApplicationHasUnboundAnnotationVar :: Int -> [ApplicationOrInstantiation] -> Bool
annotationApplicationHasUnboundAnnotationVar scope application = any (annotationHasUnboundAnnotationVar False scope) (application >>= aoiFlattenAnnotations)

-- Checks whether an annotation has unbound annotation variable
annotationHasUnboundAnnotationVar :: Bool -> Int -> Annotation -> Bool
annotationHasUnboundAnnotationVar exact minScope (AFix _ _ a1 a2) = annotationHasUnboundAnnotationVar exact minScope a1 || annotationHasUnboundAnnotationVar exact minScope a2
annotationHasUnboundAnnotationVar exact minScope (AForall a) = annotationHasUnboundAnnotationVar exact minScope a
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

-- Substitutes all free variables with bottom
-- Assumes that all fixpoints are in a first order fixpoint
annotationToFirstOrder :: HandleFixpointArgument -> Int -> Annotation -> Annotation
annotationToFirstOrder fixpointArgument@(HandleFixpointArgumentIterateNested fixpointScope) minScope (AFix _ fixRegions a1 a2)
  | annotationHasUnboundAnnotationVar True fixpointScope a2 = case fixRegions of
    FixRegionsNone -> AApp
      (annotationToFirstOrder fixpointArgument minScope a2)
      (ArgumentValue $ annotationToFirstOrder fixpointArgument minScope a1)
      (ArgumentList [])
    FixRegionsEscape arity sort ->
      let
        argRegion = sortArgumentToArgument 1 sort
      in
        annotationToFirstOrder fixpointArgument minScope $ ALam sortArgumentEmpty sort $ AApp (annotationIncrementScope 1 0 a2) (ArgumentValue $ annotationIncrementScope 1 0 a1) argRegion
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

annotationUpdateLowerbounds :: [(Int, Annotation)] -> Annotation -> Annotation
annotationUpdateLowerbounds bounds = update
  where
    boundsMap = IntMap.fromListWith (error "annotationUpdateLowerbounds: got duplicate lowerbound for a fixpoint") bounds
    update :: Annotation -> Annotation
    update (AFix identifier fixRegions lower a) =
      AFix identifier fixRegions lower' $ update a
      where
        lower' = case identifier >>= (\idx -> IntMap.lookup idx boundsMap) of
          Nothing -> lower
          Just l -> l
    update (AForall a) = AForall $ update a
    update (ALam argA argR a) = ALam argA argR $ update a
    update (AApp a argA argR) = AApp (update a) (fmap update argA) argR
    update (AInstantiate a tp) = AInstantiate (update a) tp
    update (AJoin a1 a2) = AJoin (update a1) (update a2)
    update a = a

annotationUsedRegionVariables :: Annotation -> IntSet
annotationUsedRegionVariables (ALam _ _ annotation) = used 1 annotation
  where
    used :: Int -> Annotation -> IntSet
    used scope (AFix _ _ a1 a2) = IntSet.union (used scope a1) (used scope a2)
    used scope (AForall a) = used scope a
    used scope (ALam _ _ a) = used (scope + 1) a
    used scope (AApp a argA argR) = u'
      where
        u = foldr IntSet.union (used scope a) $ map (used scope) (argumentFlatten argA)
        u' = addVars scope (argumentFlatten argR) u
    used scope (AInstantiate a _) = used scope a
    used scope (ARelation constraints) = IntSet.fromList (constraints >>= (\(Outlives (RegionVar r1) (RegionVar r2)) -> [r1, r2]))
    used scope (AJoin a1 a2) = IntSet.union (used scope a1) (used scope a2)
    used _ _ = IntSet.empty
    
    addVar :: Int -> RegionVar -> IntSet -> IntSet
    addVar scope var
      | indexBoundLambda var /= scope = id
      | otherwise = IntSet.insert $ indexInArgument var

    addVars :: Int -> [RegionVar] -> IntSet -> IntSet
    addVars scope = flip $ foldr (addVar scope)
annotationUsedRegionVariables ABottom = IntSet.empty
annotationUsedRegionVariables a = error $ "annotationUsedRegionVariables: expected lambda, got " ++ show a

annotationArgumentRemoveUnusedRegionArguments :: Argument Annotation -> ([Maybe Int], Argument Annotation)
annotationArgumentRemoveUnusedRegionArguments arguments@(ArgumentList []) = ([], arguments)
annotationArgumentRemoveUnusedRegionArguments arguments = (mapping, fmap substitute arguments)
  where
    used = IntSet.unions $ map annotationUsedRegionVariables $ argumentFlatten arguments

    regions = case filter (ABottom /=) $ argumentFlatten arguments of
      ALam _ (SortArgumentList regions) _ : _ -> regions
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
    substitute (ALam _ _ a) = ALam
      (SortArgumentList [])
      (SortArgumentList $ replicate regionCount $ SortArgumentMonomorphic SortArgumentRegion)
      $ annotationSubstitute' [] [substitution] 2 0 $ annotationIncrementScope 1 0 a
    substitute ABottom = ABottom
    substitute a = error $ "annotationArgumentRemoveUnusedRegionArguments: expected lambda, got " ++ show a

type SortEnv = [[Maybe Sort]]
annotationSaturate :: EffectEnvironment -> Annotation -> Annotation
annotationSaturate effectEnv = saturate []
  where
    saturate :: SortEnv -> Annotation -> Annotation
    -- Fixpoints should already be saturated
    saturate env (AFix identifier fixRegions a1 a2) = AFix identifier fixRegions (saturate env a1) (saturate env a2)
    saturate env a@AApp{} = saturateApp env a
    saturate env a@AInstantiate{} = saturateApp env a
    saturate env a@AVar{} = saturateApp env a
    saturate env (AForall a) = AForall $ saturate env a
    saturate env (ALam argAnnotation argRegion a) = ALam argAnnotation argRegion $ saturate env' a
      where
        env' = map f (sortArgumentFlatten argAnnotation) : env
        f (SortArgumentMonomorphic s) = Just s
        f _ = Nothing
    saturate env (AJoin a1 a2) = AJoin (saturate env a1) (saturate env a2)
    saturate env a = a -- ARelation, ABottom

    -- Argument must be a AApp, AInstantiate or AVar
    saturateApp :: SortEnv -> Annotation -> Annotation
    saturateApp env a = case saturateAndSort env a of
      (Just s, a') -> annotationSaturateWithSort s a'
      (Nothing, a') -> a'

    saturateAndSort :: SortEnv -> Annotation -> (Maybe Sort, Annotation)
    saturateAndSort env (AVar var) = case tryIndex env (indexBoundLambda var - 1) of
      Nothing -> (Nothing, AVar var)
      Just sorts -> (sorts !!! indexInArgument var, AVar var)
    saturateAndSort env (AJoin a1 a2) = (s1 <|> s2, AJoin a1' a2')
      where
        (s1, a1') = saturateAndSort env a1
        (s2, a2') = saturateAndSort env a2
    saturateAndSort env (AApp a argA argR) = (appSort <$> s, AApp a' argA' argR)
      where
        (s, a') = saturateAndSort env a
        argA' = fmap (saturate env) argA
    saturateAndSort env (AInstantiate a tp) = ((\sort -> sortInstantiate effectEnv sort []) <$> s, AInstantiate a' tp)
      where
        (s, a') = saturateAndSort env a
    saturateAndSort env a = (Nothing, saturate env a)

    appSort :: Sort -> Sort
    appSort (SortFun _ _ s) = s
    appSort s = error $ "annotationSaturate: expected sort s_1 -> s_2, got " ++ show s

annotationSaturateWithSort :: Sort -> Annotation -> Annotation
annotationSaturateWithSort annotationSort annotation = addForallsLambdas 0 0 annotationSort
  where
    -- Adds foralls and lambdas for all remaining arguments
    addForallsLambdas :: Int -> Int -> Sort -> Annotation
    addForallsLambdas lambdas foralls (SortForall s) = AForall $ addForallsLambdas lambdas (foralls + 1) s
    addForallsLambdas lambdas foralls (SortFun sortA sortR s) = ALam sortA sortR $ addForallsLambdas (lambdas + 1) foralls s
    addForallsLambdas lambdas foralls _ = applications lambdas foralls annotationSort (annotationIncrementScope lambdas foralls annotation)

    applications :: Int -> Int -> Sort -> Annotation -> Annotation
    applications lambdas foralls (SortForall s) a = applications lambdas (foralls - 1) s $ AInstantiate a (TpVar $ TypeVar foralls)
    applications lambdas foralls (SortFun sortA sortR s) a = applications (lambdas - 1) foralls s $ AApp a (AVar <$> sortArgumentToArgument (lambdas + 1) sortA) (sortArgumentToArgument lambdas sortR)
    applications 0 0 _ a = a
    applications _ _ _ _ = error "annotationSaturateWithSort: error in lambda and forall count"
{-
data Annotation
  = AFix !(Maybe Int) !FixRegions !Annotation !Annotation

  | AForall !Annotation
  | ALam !(SortArgument Sort) !(SortArgument SortArgumentRegion) !Annotation

  | AApp !Annotation !(Argument Annotation) !(Argument RegionVar)
  | AInstantiate !Annotation !Tp

  -- Leaf
  | AVar !AnnotationVar
  | ARelation ![RelationConstraint]
  | ABottom

  | AJoin !Annotation !Annotation
  deriving (Eq, Ord)
-}
