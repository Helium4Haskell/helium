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
  = AFix !(Maybe Int) !FixRegions !Annotation !Annotation

  | AForall !Annotation
  | ALam !(Argument Sort) !(Argument SortArgumentRegion) !Annotation

  | AApp !Annotation !(Argument Annotation) !(Argument RegionVar)
  | AInstantiate !Annotation !Tp

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
  show (AFix identifier fixRegions lowerBound annotation) = "fix" ++ identifierString ++ keyword ++ " " ++ lowerBoundString ++ show annotation
    where
      identifierString = case identifier of
        Nothing -> ""
        Just idx -> "[" ++ show idx ++ "]"
      keyword = case fixRegions of 
        FixRegionsNone -> ""
        FixRegionsEscape arity s -> " escape[" ++ show arity ++ "; " ++ show s ++ "] "
      lowerBoundString = case lowerBound of
        ABottom -> ". "
        _ -> "⊐ " ++ show lowerBound ++ ". "
  show (AForall annotation) = "∀ " ++ show annotation
  show (ALam annotationParams regionParams annotation) = "λ[" ++ show annotationParams ++ "; " ++ show regionParams ++ "] -> " ++ show annotation
  show annotation = showAnnotationJoin annotation

showAnnotationJoin :: Annotation -> String
showAnnotationJoin (AJoin a1 a2) = showAnnotationApp a1 ++ " ⊔ " ++ showAnnotationJoin a2
showAnnotationJoin annotation = showAnnotationApp annotation

showAnnotationApp :: Annotation -> String
showAnnotationApp (AApp annotation annotationArgs regionArgs) =
  showAnnotationApp annotation ++ " [" ++ show annotationArgs ++ "; " ++ show regionArgs ++ "]"
showAnnotationApp (AInstantiate a tp) = showAnnotationApp a ++ " {" ++ show tp ++ "}"
showAnnotationApp annotation = showAnnotationLow annotation

showAnnotationLow :: Annotation -> String
showAnnotationLow (AVar var) = show var
showAnnotationLow (ARelation rel) = show rel
showAnnotationLow ABottom = "⊥"
showAnnotationLow annotation = "(" ++ show annotation ++ ")"

annotationExpandBottom :: Sort -> Annotation
annotationExpandBottom (SortForall sort) = AForall $ annotationExpandBottom sort
annotationExpandBottom (SortFun annotationArgs regionArgs sort) =
  ALam annotationArgs regionArgs $ annotationExpandBottom sort
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

zipArgument :: (a -> b -> c) -> Argument a -> Argument b -> Argument c
zipArgument f (ArgumentValue a) (ArgumentValue b) = ArgumentValue $ f a b
zipArgument f (ArgumentList as) (ArgumentList bs) = ArgumentList $ zipWith (zipArgument f) as bs
zipArgument _ _ _ = error "zipArgument: Arguments do not have the same sort"

zipFlattenArgumentWithSort :: (Show a, Show b, Show s) => (s -> a -> b -> c) -> Argument s -> Argument a -> Argument b -> [c]
zipFlattenArgumentWithSort f sort argLeft argRight = zipFlattenArgumentWithSort' sort argLeft argRight []
  where
    zipFlattenArgumentWithSort' (ArgumentValue s) (ArgumentValue a) (ArgumentValue b) accum = f s a b : accum
    zipFlattenArgumentWithSort' (ArgumentList sorts) (ArgumentList as) (ArgumentList bs) accum = foldr (\(s, a, b) -> zipFlattenArgumentWithSort' s a b) accum $ zip3 sorts as bs
    zipFlattenArgumentWithSort' sorts a b accum = error $ "zipFlattenArgumentWithSort: Arguments do not have the same sort: " ++ show sorts ++ "; " ++ show a ++ "; " ++ show b

annotationEscapes :: Int -> Annotation -> IntSet
annotationEscapes arity annotation = IntSet.map (indexInArgument . RegionVar) $ IntSet.filter isFirstScope escapes
  where
    (annotationRelation, annotationRoots) = gather 1 annotation

    escapes = case annotationRelation of
      Nothing -> annotationRoots
      Just rel -> IntSet.foldr (relationDFS' (const False) rel . RegionVar) IntSet.empty annotationRoots

    gather :: Int -> Annotation -> (Maybe Relation, IntSet)
    gather scope (AFix _ _ a1 _) = gather scope a1
    gather scope (AForall a) = gather scope a
    gather scope (ALam _ sortArgR a) = decrement $ addVars scope vars $ gather (scope + 1) a
      where
        argR = sortArgumentToArgument 1 sortArgR
        vars
          -- Don't add the arguments, corresponding with the method arguments, to the root set
          | scope <= arity = []
          -- Add these arguments to the root set. They origin from the return value of a method, returning
          -- a function or an object containing functions.
          | otherwise = argumentFlatten argR
    -- TODO: Don't add region arguments of last argument in a call (eg the return regions)
    gather scope (AApp a argA argR) = addVars scope (argumentFlatten argR) (gather scope a) `join` joins (map (gather scope) $ argumentFlatten argA)
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
    addVar scope var tuple@(relation, set)
      | indexBoundLambda var == scope = (relation, IntSet.insert (indexInArgument var) set)
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

annotationFilterInternalRegions :: Int -> Annotation -> Annotation
annotationFilterInternalRegions arity annotation = filter 1 annotation
  where
    escapes = annotationEscapes arity annotation

    filter :: Int -> Annotation -> Annotation
    filter scope (AFix identifier fixRegions a1 a2) = AFix identifier fixRegions (filter scope a1) (filter scope a2)
    filter scope (AForall a) = AForall $ filter scope a
    filter scope (ALam argA argR a) = ALam argA argR $ filter (scope + 1) a
    filter scope (AApp a argA argR) = AApp (filter scope a) (filter scope <$> argA) argR
    filter scope (AInstantiate a tp) = AInstantiate (filter scope a) tp
    filter scope (ARelation constraints) = ARelation $ mapMaybe (filterRelationConstraint scope) constraints
    filter scope (AJoin a1 a2) = AJoin (filter scope a1) (filter scope a2)
    filter _ a = a

    filterRelationConstraint scope c@(Outlives r1 r2)
      | preserve scope r1 && preserve scope r2 = Just c
      | otherwise = Nothing

    -- A variable is preserved if it is either from a different scope,
    -- or it is the scope of additional region args and the region escapes according to annotationEscapes
    preserve :: Int -> RegionVar -> Bool
    preserve scope var = indexBoundLambda var /= scope || indexInArgument var `IntSet.member` escapes

annotationRemoveInternalRegions :: Int -> Argument SortArgumentRegion -> Annotation -> (Argument SortArgumentRegion, Annotation)
annotationRemoveInternalRegions arity (ArgumentList regionArgs) a = (ArgumentList regionArgs', substitute 1 a)
  where
    argCount = length regionArgs

    escapes = annotationEscapes arity a

    regionArgs' = map snd $ filter (isJust . fst) $ zip mapping regionArgs

    mapping :: [Maybe Int]
    mapping = assignIndices 0 0

    assignIndices :: Int -> Int -> [Maybe Int]
    assignIndices var fresh
      | var == argCount = []
      | var `IntSet.notMember` escapes = Nothing : assignIndices (var + 1) fresh
      | otherwise = Just fresh : assignIndices (var + 1) (fresh + 1)

    substitute :: Int -> Annotation -> Annotation
    substitute scope (AFix identifier fixRegions a1 a2) = AFix identifier fixRegions (substitute scope a1) (substitute scope a2)
    substitute scope (AForall a) = AForall $ substitute scope a
    substitute scope (ALam argA argR a) = ALam argA argR $ substitute (scope + 1) a
    substitute scope (AApp a argA argR) = AApp (substitute scope a) (substitute scope <$> argA) (substituteVar scope <$> argR)
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
