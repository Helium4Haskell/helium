module Helium.CodeGeneration.Iridium.Region.Annotation where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import qualified Data.Graph as Graph

import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Utils

newtype AnnotationVar = AnnotationVar { unAnnotationVar :: Int }
  deriving (Eq, Ord)

instance IndexVariable AnnotationVar where
  variableToInt (AnnotationVar i) = i
  variableFromInt i = AnnotationVar i

instance Show AnnotationVar where
  show var = 'ψ' : showIndexVariable var

data Annotation
  = AFix !FixRegions !(Argument Sort) !(Argument Annotation)

  | AForall !Annotation
  | ALam !(Argument Sort) !(Argument SortArgumentRegion) !RegionDirection !Annotation

  | AApp !Annotation !(Argument Annotation) !(Argument RegionVar) !RegionDirection
  | AInstantiate !Annotation !Tp

  | ATuple ![Annotation]
  | AProject !Annotation !Int

  -- Leaf
  | AVar !AnnotationVar
  | ARelation ![RelationConstraint]
  | ABottom

  | AJoin !Annotation !Annotation
  deriving (Eq, Ord)

data FixRegions
  = FixRegionsNone
  | FixRegionsEscape !Int !(Argument SortArgumentRegion)
  deriving (Eq, Ord)

instance Show Annotation where
  show (AFix fixRegions sort annotation) = "fix" ++ keyword ++ show sort ++ ". " ++ show annotation
    where
      keyword = case fixRegions of 
        FixRegionsNone -> ": "
        FixRegionsEscape arity s -> " escape[" ++ show arity ++ "; " ++ show s ++ "]: "
  show (AForall annotation) = "∀ " ++ show annotation
  show (ALam annotationParams regionParams dir annotation) = "λ[" ++ show annotationParams ++ "; " ++ show regionParams ++ "]" ++ show dir ++ " -> " ++ show annotation
  show annotation = showAnnotationJoin annotation

showAnnotationJoin :: Annotation -> String
showAnnotationJoin (AJoin a1 a2) = showAnnotationApp a1 ++ " ⊔ " ++ showAnnotationJoin a2
showAnnotationJoin annotation = showAnnotationApp annotation

showAnnotationApp :: Annotation -> String
showAnnotationApp (AApp annotation annotationArgs regionArgs dir) =
  showAnnotationApp annotation ++ " [" ++ show annotationArgs ++ "; " ++ show regionArgs ++ "]" ++ show dir
showAnnotationApp (AInstantiate a tp) = showAnnotationApp a ++ " {" ++ show tp ++ "}"
showAnnotationApp annotation = showAnnotationLow annotation

showAnnotationLow :: Annotation -> String
showAnnotationLow (AVar var) = show var
showAnnotationLow (ARelation rel) = show rel
showAnnotationLow ABottom = "⊥"
showAnnotationLow (ATuple as) = "tuple(" ++ intercalate ", " (map show as) ++ ")"
showAnnotationLow (AProject a idx) = "project(" ++ show a ++ ", " ++ show idx ++ ")"
showAnnotationLow annotation = "⦅" ++ show annotation ++ "⦆"

annotationExpandBottom :: Sort -> Annotation
annotationExpandBottom (SortForall sort) = AForall $ annotationExpandBottom sort
annotationExpandBottom (SortFun annotationArgs regionArgs dir sort) =
  ALam annotationArgs regionArgs dir $ annotationExpandBottom sort
annotationExpandBottom SortRelation = ARelation []

sortArgumentToArgument :: IndexVariable var => Int -> Argument a -> Argument var
sortArgumentToArgument lambdaBound arg = snd $ sortArgumentToArgument' lambdaBound 0 arg

sortArgumentToArgument' :: IndexVariable var => Int -> Int -> Argument a -> (Int, Argument var)
sortArgumentToArgument' lambdaBound idx (ArgumentValue a) = (idx + 1, ArgumentValue $ variableFromIndices lambdaBound idx)
sortArgumentToArgument' lambdaBound idx (ArgumentList args) = (idx', ArgumentList params)
  where
    (idx', params) = mapAccumL (sortArgumentToArgument' lambdaBound) idx args

zipFlattenArgument :: (Show a, Show b) => (a -> b -> c) -> Argument a -> Argument b -> [c]
zipFlattenArgument f argLeft argRight = zipFlattenArgument' argLeft argRight []
  where
    zipFlattenArgument' (ArgumentValue a) (ArgumentValue b) accum = f a b : accum
    zipFlattenArgument' (ArgumentList as) (ArgumentList bs) accum = foldr (\(a, b) -> zipFlattenArgument' a b) accum $ zip as bs
    zipFlattenArgument' a b accum = error $ "zipFlattenArgument: Arguments do not have the same sort: " ++ show a ++ "; " ++ show b

zipArgument :: (Show a, Show b) => (a -> b -> c) -> Argument a -> Argument b -> Argument c
zipArgument f (ArgumentValue a) (ArgumentValue b) = ArgumentValue $ f a b
zipArgument f (ArgumentList as) (ArgumentList bs)
  | length as /= length bs = error $ "zipArgument: Arguments do not have the same sort:\n" ++ show as ++ "\n" ++ show bs
  | otherwise = ArgumentList $ zipWith (zipArgument f) as bs
zipArgument _ as bs = error $ "zipArgument: Arguments do not have the same sort:\n" ++ show as ++ "\n" ++ show bs

zipFlattenArgumentWithSort :: (Show a, Show b, Show s) => (s -> a -> b -> c) -> Argument s -> Argument a -> Argument b -> [c]
zipFlattenArgumentWithSort f sort argLeft argRight = zipFlattenArgumentWithSort' sort argLeft argRight []
  where
    zipFlattenArgumentWithSort' (ArgumentValue s) (ArgumentValue a) (ArgumentValue b) accum = f s a b : accum
    zipFlattenArgumentWithSort' (ArgumentList sorts) (ArgumentList as) (ArgumentList bs) accum = foldr (\(s, a, b) -> zipFlattenArgumentWithSort' s a b) accum $ zip3 sorts as bs
    zipFlattenArgumentWithSort' sorts a b accum = error $ "zipFlattenArgumentWithSort: Arguments do not have the same sort: " ++ show sorts ++ "; " ++ show a ++ "; " ++ show b

annotationUsedRegionVariables :: Bool -> Annotation -> IntSet
annotationUsedRegionVariables skipRegionDirectionOutlives (ALam _ _ _ annotation) = used 1 annotation
  where
    used :: Int -> Annotation -> IntSet
    used scope (AFix _ _ a) = IntSet.unions $ used scope <$> argumentFlatten a
    used scope (ATuple as) = IntSet.unions $ used scope <$> as
    used scope (AProject a idx) = used scope a
    used scope (AForall a) = used scope a
    used scope (ALam _ _ _ a) = used (scope + 1) a
    used scope (AApp a argA argR dir) = u'
      where
        u = foldr IntSet.union (used scope a) $ map (used scope) (argumentFlatten argA)
        u'
          | skipRegionDirectionOutlives && dir == RegionDirectionOutlives = u
          | otherwise = addVars scope (argumentFlatten argR) u
    used scope (AInstantiate a _) = used scope a
    used scope (ARelation constraints) = IntSet.fromList (constraints >>= (\(Outlives r1 r2) -> f r1 ++ f r2))
      where
        f r
          | indexBoundLambda r == scope = [indexInArgument r]
          | otherwise = []
    used scope (AJoin a1 a2) = IntSet.union (used scope a1) (used scope a2)
    used _ _ = IntSet.empty
    
    addVar :: Int -> RegionVar -> IntSet -> IntSet
    addVar scope var
      | indexBoundLambda var /= scope = id
      | otherwise = IntSet.insert $ indexInArgument var

    addVars :: Int -> [RegionVar] -> IntSet -> IntSet
    addVars scope = flip $ foldr (addVar scope)
annotationUsedRegionVariables _ ABottom = IntSet.empty
annotationUsedRegionVariables _ a = error $ "annotationUsedRegionVariables: expected lambda, got " ++ show a

annotationEscapes :: Int -> Annotation -> IntSet
annotationEscapes arity annotation = IntSet.map (indexInArgument . RegionVar) $ IntSet.filter isFirstScope escapes
  where
    (annotationRelation, annotationRoots) = gather 1 annotation

    escapes = case annotationRelation of
      Nothing -> annotationRoots
      Just rel -> IntSet.foldr (relationDFS' (const False) rel . RegionVar) IntSet.empty annotationRoots

    gather :: Int -> Annotation -> (Maybe Relation, IntSet)
    gather scope (AFix _ _ a1) = joins $ gather scope <$> argumentFlatten a1
    gather scope (ATuple as) = joins $ gather scope <$> as
    gather scope (AProject a _) = gather scope a
    gather scope (AForall a) = gather scope a
    gather scope (ALam _ sortArgR _ a) = decrement $ addVars scope vars $ gather (scope + 1) a
      where
        argR = sortArgumentToArgument 1 sortArgR
        vars
          -- Don't add the arguments, corresponding with the method arguments, to the root set
          | scope <= arity = []
          -- Add these arguments to the root set. They origin from the return value of a method, returning
          -- a function or an object containing functions.
          | otherwise = argumentFlatten argR
    -- Don't add region arguments of last argument in a call (eg the return regions)
    gather scope (AApp a argA argR dir) = case dir of
      RegionDirectionAny -> addVars scope (argumentFlatten argR) result
      RegionDirectionOutlives -> result
      where
        result = gather scope a `join` joins (map (gather scope) $ argumentFlatten argA)
    gather scope (AInstantiate a _) = gather scope a
    gather scope (AJoin a1 a2) = gather scope a1 `join` gather scope a2
    gather scope (ARelation constraints) = (Just $ relationFromTransitiveConstraints constraints, IntSet.empty)
    gather _ _ = (Nothing, IntSet.empty)

    joins :: [(Maybe Relation, IntSet)] -> (Maybe Relation, IntSet)
    joins (r:rs) = foldr join r rs
    joins [] = (Nothing, IntSet.empty)

    join :: (Maybe Relation, IntSet) -> (Maybe Relation, IntSet) -> (Maybe Relation, IntSet)
    join (relation1, set1) (relation2, set2) = (relation, IntSet.union set1 set2)
      where
        relation = case relation1 of
          Nothing -> relation2
          Just r1 -> case relation2 of
            Just r2 -> Just $ relationUnion r1 r2
            Nothing -> Just r1

    addVar :: Int -> RegionVar -> (Maybe Relation, IntSet) -> (Maybe Relation, IntSet)
    addVar scope var@(RegionVar idx) tuple@(relation, set)
      | indexBoundLambda var == scope = (relation, IntSet.insert {-(indexInArgument var)-}idx set)
      | otherwise = tuple

    addVars scope = flip $ foldr $ addVar scope

    decrement :: (Maybe Relation, IntSet) -> (Maybe Relation, IntSet)
    decrement (Nothing, roots) = (Nothing, decrementSet $ IntSet.filter (not . isFirstScope) roots)
    decrement (Just r, roots) = (Just $ relationDecrementScope r, dfsFirstScope r roots)

    decrementSet :: IntSet -> IntSet
    decrementSet set = IntSet.map dec set
      where
        dec r = let RegionVar r' = variableIncrementLambdaBound 1 (-1) $ RegionVar r in r'

    isFirstScope :: Int -> Bool
    isFirstScope idx = indexBoundLambda (RegionVar idx) == 1

    -- Apply DFS until we reach a variable outside of the first scope
    dfsFirstScope :: Relation -> IntSet -> IntSet
    dfsFirstScope relation roots
      = decrementSet
      $ IntSet.filter (not . isFirstScope)
      $ IntSet.foldr f first rest
      where
        f idx = relationDFS' (\(RegionVar r) -> not $ isFirstScope r) relation (RegionVar idx)
        (first, rest) = IntSet.partition isFirstScope roots

annotationBaseRelation :: Annotation -> [RelationConstraint]
annotationBaseRelation (AForall a) = annotationBaseRelation a
annotationBaseRelation (ALam _ _ _ a) = annotationBaseRelation a
annotationBaseRelation (AJoin (ARelation cs) _) = cs
annotationBaseRelation (AJoin _ a) = annotationBaseRelation a
annotationBaseRelation (ARelation cs) = cs
annotationBaseRelation _ = []

annotationRemoveBaseRelation :: Annotation -> Annotation
annotationRemoveBaseRelation (AForall a) = AForall $ annotationRemoveBaseRelation a
annotationRemoveBaseRelation (ALam argA argR dir a) = ALam argA argR dir $ annotationRemoveBaseRelation a
annotationRemoveBaseRelation (AJoin a1 a2) = AJoin (annotationRemoveBaseRelation a1) (annotationRemoveBaseRelation a2)
annotationRemoveBaseRelation (ARelation a) = ABottom
annotationRemoveBaseRelation a = a

annotationFilterInternalRegions :: Int -> Argument Annotation -> (IntSet, Argument Annotation)
annotationFilterInternalRegions arity annotation = (escapes, filterAnnotation 0 <$> annotation)
  where
    escapes = IntSet.unions $ lambdaEscapes <$> argumentFlatten annotation

    lambdaEscapes (ALam _ _ _ a) = annotationEscapes arity a
    lambdaEscapes ABottom = IntSet.empty

    filterAnnotation :: Int -> Annotation -> Annotation
    filterAnnotation scope (AFix fixRegions sort a) = AFix fixRegions sort (filterAnnotation scope <$> a)
    filterAnnotation scope (AForall a) = AForall $ filterAnnotation scope a
    filterAnnotation scope (ATuple as) = ATuple $ map (filterAnnotation scope) as
    filterAnnotation scope (AProject a idx) = AProject (filterAnnotation scope a) idx
    filterAnnotation scope (ALam argA argR dir a) = ALam argA argR dir $ filterAnnotation (scope + 1) a
    filterAnnotation scope (AApp a argA argR dir) = AApp (filterAnnotation scope a) (filterAnnotation scope <$> argA) argR' dir
      where
        argR' :: Argument RegionVar
        argR' = case dir of
          RegionDirectionOutlives -> mapRegionVariable scope <$> argR
          RegionDirectionAny
            | all (preserve scope) $ argumentFlatten argR -> argR
            | otherwise -> error $ "Argument is not preserved, but was used in an application: " ++ show (filter (not . preserve scope) $ argumentFlatten argR) ++ "\n" ++ show annotation ++ "\n" ++ show (map RegionVar $ IntSet.toList escapes)
    filterAnnotation scope (AInstantiate a tp) = AInstantiate (filterAnnotation scope a) tp
    filterAnnotation scope (ARelation constraints) = ARelation $ mapMaybe (filterRelationConstraint scope) constraints
    filterAnnotation scope (AJoin a1 a2) = AJoin (filterAnnotation scope a1) (filterAnnotation scope a2)
    filterAnnotation _ a = a

    filterRelationConstraint scope c@(Outlives r1 r2)
      | preserve scope r1 && preserve scope r2 = Just c
      | otherwise = Nothing

    mapRegionVariable :: Int -> RegionVar -> RegionVar
    mapRegionVariable scope r
      | preserve scope r = r
      | otherwise = regionBottom

    -- A variable is preserved if it is either from a different scope,
    -- or it is the scope of additional region args and the region escapes according to annotationEscapes
    preserve :: Int -> RegionVar -> Bool
    preserve scope var = indexBoundLambda var /= scope || indexInArgument var `IntSet.member` escapes
{-
annotationRemoveInternalRegions :: Int -> Argument SortArgumentRegion -> Annotation -> (Argument SortArgumentRegion, Annotation)
annotationRemoveInternalRegions arity (ArgumentList regionArgs) a@(ALam _ _ _ a') = (ArgumentList regionArgs', substitute 1 a)
  where
    argCount = length regionArgs

    escapes = annotationEscapes arity a'

    regionArgs' = map snd $ filter (isJust . fst) $ zip mapping regionArgs

    mapping :: [Maybe Int]
    mapping = assignIndices 0 0

    assignIndices :: Int -> Int -> [Maybe Int]
    assignIndices var fresh
      | var == argCount = []
      | var' `IntSet.notMember` escapes = Nothing : assignIndices (var + 1) fresh
      | otherwise = Just fresh : assignIndices (var + 1) (fresh + 1)
      where
        RegionVar var' = variableFromIndices 1 var

    substitute :: Int -> Annotation -> Annotation
    substitute scope (AFix fixRegions sort a) = AFix fixRegions sort $ substitute scope <$> a
    substitute scope (AForall a) = AForall $ substitute scope a
    substitute scope (AProject a idx) = AProject (substitute scope a) idx
    substitute scope (ATuple as) = ATuple $ fmap (substitute scope) as
    substitute scope (ALam argA argR dir a) = ALam argA argR dir $ substitute (scope + 1) a
    substitute scope (AApp a argA argR dir) = AApp (substitute scope a) (substitute scope <$> argA) (substituteVar scope <$> argR) dir
    substitute scope (AInstantiate a tp) = AInstantiate (substitute scope a) tp
    substitute scope (ARelation constraints) = ARelation $ mapMaybe (substituteRelationConstraint scope) constraints
    substitute scope (AJoin a1 a2) = AJoin (substitute scope a1) (substitute scope a2)
    substitute _ a = a

    substituteRelationConstraint :: Int -> RelationConstraint -> Maybe RelationConstraint
    substituteRelationConstraint scope (Outlives r1 r2) =
      Outlives <$> substituteVarMaybe scope r1 <*> substituteVarMaybe scope r2

    substituteVar :: Int -> RegionVar -> RegionVar
    substituteVar scope var = case substituteVarMaybe scope var of
      Nothing -> error "annotationRemoveInternalRegions: forced substitution failed: variable was needed, but was also removed (internal)"
      Just var' -> var'

    substituteVarMaybe :: Int -> RegionVar -> Maybe RegionVar
    substituteVarMaybe scope var
      | indexBoundLambda var /= scope = Just var
      | otherwise = variableFromIndices scope <$> mapping !!! indexInArgument var
-}
argumentShapeEqual :: Argument a -> Argument b -> Bool
argumentShapeEqual (ArgumentValue _) (ArgumentValue _) = True
argumentShapeEqual (ArgumentList as) (ArgumentList bs)
  | length as == length bs = all (uncurry argumentShapeEqual) $ zip as bs
argumentShapeEqual _ _ = False
