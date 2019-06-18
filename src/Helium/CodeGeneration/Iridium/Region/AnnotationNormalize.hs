module Helium.CodeGeneration.Iridium.Region.AnnotationNormalize (annotationNormalize, annotationIncrementScope) where

import Data.List
import Data.Maybe
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

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
    relation = case [c | ARelation constraints <- as, c <- constraints] of
      [] -> []
      constraints -> [ARelation constraints] -- TODO: Compute transitive closure when joining multiple ARelations

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

annotationApplyLambda :: Annotation -> [ApplicationOrInstantiation] -> [[Annotation]] -> [[RegionVar]] -> (Annotation, [ApplicationOrInstantiation])
annotationApplyLambda ABottom _ _ _ = (ABottom, [])
annotationApplyLambda (ALam _ _ a) (AOIApplication argA argR : args) aSubst rSubst
  = annotationApplyLambda a args (argumentFlatten argA : aSubst) (argumentFlatten argR : rSubst)
  -- TODO: Allow applying a polymorphic argument with a monomorphic region variable
annotationApplyLambda a args [] [] = (a, args)
annotationApplyLambda a args aSubst rSubst
  = (annotationSubstitute aSubst rSubst a, args)
{- annotationApplyLambda env a aArgs rArgs aSubst rSubst -- Oversaturated
  = as >>= evalFurther
  where
    as = annotationNormalize'' env $ if null aSubst then a else annotationSubstitute aSubst rSubst a
    evalFurther a'
      -- Can evaluate further
      | canEval = annotationApplyLambda env a' aArgs rArgs [] []
      -- Cannot evaluate further. Add remaining arguments
      | otherwise = return $ foldl (\a'' (aArg, rArg) -> AApp a'' aArg rArg) a' $ zip aArgs rArgs
      where
        canEval = case a' of
          ALam _ _ _ -> True
          AJoin _ _ -> True
          AFix _ _ _ _ -> True
          _ -> False -}

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
      | lambdaIndex > firstLambda + count = AVar $ variableFromIndices (lambdaIndex - firstLambda) argumentIndex
      | otherwise = (substitutionAnnotation !! (lambdaIndex - firstLambda)) !! argumentIndex
      where
        lambdaIndex = indexBoundLambda var
        argumentIndex = indexInArgument var
    substitute firstLambda forallNesting (ARelation cs) =
      ARelation $ map (\(Outlives r1 r2) -> Outlives (substituteRegionVar firstLambda r1) (substituteRegionVar firstLambda r2)) cs
    substitute firstLambda forallNesting ABottom = ABottom
    substitute firstLambda forallNesting (AJoin a1 a2) = substitute firstLambda forallNesting a1 `AJoin` substitute firstLambda forallNesting a2

    substituteRegionVar :: Int -> RegionVar -> RegionVar
    substituteRegionVar firstLambda var
      | lambdaIndex < firstLambda = var
      | lambdaIndex > firstLambda + count = variableFromIndices (lambdaIndex - count) argumentIndex
      | otherwise = (substitutionRegion !! (lambdaIndex - firstLambda)) !! argumentIndex
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
  Just lambdaSubst -> fmap (variableFromIndices lambda) $ lambdaSubst !! indexInArgument var
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
annotationIterate env identifier fixRegions lowerBound (ALam argA argR function) mainApplication = (AFix identifier fixRegions annotationFinal $ ALam argA argR functionFinal, annotationFinal)
  where
    (functionFinal, annotationFinal) = iterate (annotationNormalize env function) (annotationNormalize env lowerBound)

    mainApplication' = map (aoiMapAnnotation (annotationToFirstOrder HandleFixpointArgumentNone 1)) mainApplication
    mainApplicationHasUnbound = annotationApplicationHasUnboundAnnotationVar 1 mainApplication

    iterate :: Annotation -> Annotation -> (Annotation, Annotation)
    iterate function' current = case isFixed function' current next of
      FirstOrderFixpoint -> (function'', AFix identifier fixRegions next function'')
      HigherOrderFixpoint -> (function'', current)
      NoFixpoint -> iterate function'' next
      where
        application = case fixRegions of
          FixRegionsNone -> AApp function' (ArgumentValue current) (ArgumentList [])
          FixRegionsEscape sort -> ALam (SortArgumentList []) sort $ AApp function' (ArgumentValue current) (sortArgumentToArgument 0 sort)
        (info, next) = annotationNormalize' env application
        function'' = annotationUpdateLowerbounds info function'


    isFixed :: Annotation -> Annotation -> Annotation -> FixpointState
    isFixed function' previous current
      | previous == current = HigherOrderFixpoint
      | {- all undefined undefined -} False -- If all applications are fixed
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
-- TODO: Check for escaping regions

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
    FixRegionsEscape sort ->
      let
        a2' = annotationToFirstOrder fixpointArgument minScope a2
        a1' = annotationToFirstOrder fixpointArgument minScope a1
        argRegion = sortArgumentToArgument 1 sort
      in
        ALam sortArgumentEmpty sort $ AApp (annotationIncrementScope 1 0 a2') (ArgumentValue $ annotationIncrementScope 1 0 a1') argRegion
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
