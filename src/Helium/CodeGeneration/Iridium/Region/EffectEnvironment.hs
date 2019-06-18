module Helium.CodeGeneration.Iridium.Region.EffectEnvironment where

import Data.List
import Lvm.Common.IdMap
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Relation

data EffectDataType = EffectDataType
  !(SortArgument Sort) -- Annotation variables of the data type
  !(SortArgument SortArgumentRegion) -- The region variables of the data type
  ![RelationConstraint]

data EffectConstructor = EffectConstructor
  ![Argument AnnotationVar] -- Instantiation of the region and annotation variables per field of the constructor
  ![Argument RegionVar]

data EffectGlobal = EffectGlobal !Int !Tp !(Argument Annotation)

data EffectEnvironment = EffectEnvironment
  { eeDataTypes :: !(IdMap EffectDataType)
  , eeConstructors :: !(IdMap EffectConstructor)
  , eeGlobals :: !(IdMap EffectGlobal)
  }

eeLookupDataType :: EffectEnvironment -> Id -> EffectDataType
eeLookupDataType env name = case lookupMap name $ eeDataTypes env of
  Nothing -> error $ "eeLookupDataType: Could not find data type: " ++ show name
  Just dataType -> dataType

eeLookupConstructor :: EffectEnvironment -> Id -> EffectConstructor
eeLookupConstructor env name = case lookupMap name $ eeConstructors env of
  Nothing -> error $ "eeLookupConstructor: Could not find constructor: " ++ show name
  Just con -> con

eeLookupGlobal :: EffectEnvironment -> Id -> EffectGlobal
eeLookupGlobal env name = case lookupMap name $ eeGlobals env of
  Nothing -> error $ "eeLookupGlobal: Could not find value: " ++ show name
  Just con -> con

eeInsertGlobal :: Id -> EffectGlobal -> EffectEnvironment -> EffectEnvironment
eeInsertGlobal name global env = env{ eeGlobals = insertMap name global $ eeGlobals env }

eeUpdateGlobal :: Id -> (EffectGlobal -> EffectGlobal) -> EffectEnvironment -> EffectEnvironment
eeUpdateGlobal name fn env = env{ eeGlobals = insertMapWith name (error "eeUpdateGlobal: name not found") fn $ eeGlobals env }

globalHasAdditionalRegions :: EffectGlobal -> Bool
globalHasAdditionalRegions (EffectGlobal _ _ annotations) = case argumentFlatten annotations of
  [] -> False
  -- All annotation of a global should have the same additional arguments, so we only need to check the first one
  ALam _ (SortArgumentList []) _ : _ -> False
  _ -> True

instance Show EffectEnvironment where
  show (EffectEnvironment datas constructors values)
    = "DATA TYPES\n" ++ (listFromMap datas >>= showDataType)
    ++ "\n\nCONSTRUCTORS\n" ++ (listFromMap constructors >>= showConstructor)
    ++ "\n\nGLOBALS\n" ++ (listFromMap values >>= showGlobal)
    where
      showDataType (name, EffectDataType s1 s2 constraints) = show name ++ ": " ++ show s1 ++ "; " ++ show s2 ++ "; " ++ show constraints ++ "\n"
      showConstructor (name, EffectConstructor a1 a2) = show name ++ ": " ++ show a1 ++ "; " ++ show a2 ++ "\n"
      showGlobal (name, EffectGlobal arity tp args) = show name ++ "[" ++ show arity ++ "]: " ++ show tp ++ "; " ++ show args ++ "\n"

typeRegionSort :: EffectEnvironment -> Tp -> SortArgument SortArgumentRegion
typeRegionSort env tp
  | tpIsStrict tp = SortArgumentList
    [ SortArgumentMonomorphic SortArgumentRegion -- Region for the value
    , typeRegionChildSort env (tpNotStrict tp) []
    ]
  | otherwise = SortArgumentList
    [ SortArgumentMonomorphic SortArgumentRegion -- Region for the thunk
    , SortArgumentMonomorphic SortArgumentRegion -- Region for the value
    , typeRegionChildSort env tp []
    ]

typeRegionChildSort :: EffectEnvironment -> Tp -> [Tp] -> SortArgument SortArgumentRegion
typeRegionChildSort env (TpCon TConFun) _ = SortArgumentList []
typeRegionChildSort env (TpStrict _) _ = error "typeRegionChildSort: Did not expect a strictness annotation on this position"
typeRegionChildSort env (TpVar tvar) tps = SortArgumentPolymorphic tvar tps
typeRegionChildSort env (TpForall tp) [] = typeRegionChildSort env tp []
typeRegionChildSort env (TpCon (TConDataType name)) tps = snd $ eeDataTypeArguments env name tps
typeRegionChildSort env (TpCon (TConTypeClassDictionary name)) tps = snd $ eeDataTypeArguments env (dictionaryDataTypeName name) tps
typeRegionChildSort env (TpCon (TConTuple _)) tps = sort
  where
    sort = SortArgumentList $
      -- For each field, a region for the thunk, a region for the value and region variables for the fields / children of the element
      tps >>= (\tp -> [SortArgumentMonomorphic SortArgumentRegion, SortArgumentMonomorphic SortArgumentRegion, typeRegionChildSort env tp []])
typeRegionChildSort env (TpApp t1 t2) tps = typeRegionChildSort env t1 (t2 : tps)

typeAnnotationSortArgument :: EffectEnvironment -> Tp -> [Tp] -> SortArgument Sort
typeAnnotationSortArgument env (TpStrict tp) [] = typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TpForall tp) [] = fmap SortForall $ typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TpVar tvar) tps = SortArgumentPolymorphic tvar tps
typeAnnotationSortArgument env (TpCon TConFun) [tArg, tReturn] =
  fmap (SortFun annotationArg regionArg) $
    SortArgumentList
      [ SortArgumentMonomorphic
        $ SortFun sortArgumentEmpty (SortArgumentMonomorphic SortArgumentRegion)
        $ SortFun sortArgumentEmpty regionReturn SortRelation
      , annotationReturn
      ]
  where
    regionArg = typeRegionSort env tArg
    annotationArg = typeAnnotationSortArgument env tArg []
    regionReturn = typeRegionSort env (tpStrict tReturn)
    annotationReturn = typeAnnotationSortArgument env tReturn []
typeAnnotationSortArgument env (TpApp t1 t2) tps = typeAnnotationSortArgument env t1 (t2 : tps)
typeAnnotationSortArgument env (TpCon con) tps = case con of
  TConFun -> error "typeAnnotationSortArgument: Expected a type of kind *"
  TConDataType name -> fst $ eeDataTypeArguments env name tps
  TConTypeClassDictionary name -> fst $ eeDataTypeArguments env (dictionaryDataTypeName name) tps
  TConTuple _ -> SortArgumentList $ map (\tp -> typeAnnotationSortArgument env tp []) tps

eeDataTypeArguments :: EffectEnvironment -> Id -> [Tp] -> (SortArgument Sort, SortArgument SortArgumentRegion)
eeDataTypeArguments env name [] =
  -- Fast variant, if the data type does not have type arguments then we do not have to perform a substitution
  (annotationSort, regionSort)
  where
    (EffectDataType annotationSort regionSort _) = eeLookupDataType env name
eeDataTypeArguments env name types =
  ( sortArgumentAnnotationSubstitute env (TypeSubstitution 1 types) annotationSort
  , sortArgumentRegionSubstitute env (TypeSubstitution 1 types) regionSort
  )
  where
    (EffectDataType annotationSort regionSort _) = eeLookupDataType env name

sortArgumentRegionSubstitute :: EffectEnvironment -> TypeSubstitution -> SortArgument SortArgumentRegion -> SortArgument SortArgumentRegion
sortArgumentRegionSubstitute env substitution = sortArgumentSubstitute substitution (typeRegionChildSort env) id

sortArgumentAnnotationSubstitute :: EffectEnvironment -> TypeSubstitution -> SortArgument Sort -> SortArgument Sort
sortArgumentAnnotationSubstitute env substitution = sortArgumentSubstitute substitution (typeAnnotationSortArgument env) (sortSubstitute env substitution)

sortSubstitute :: EffectEnvironment -> TypeSubstitution -> Sort -> Sort
sortSubstitute env substitution SortRelation = SortRelation
sortSubstitute env (TypeSubstitution first tps) (SortForall sort)
  = SortForall $ sortSubstitute env substitution sort
  where
    substitution = TypeSubstitution (first + 1) tps
sortSubstitute env substitution (SortFun argumentAnnotation argumentRegion sort) = SortFun argumentAnnotation' argumentRegion' sort'
  where
    argumentAnnotation' = sortArgumentAnnotationSubstitute env substitution argumentAnnotation
    argumentRegion' = sortArgumentRegionSubstitute env substitution argumentRegion
    sort' = sortSubstitute env substitution sort

sortInstantiate :: EffectEnvironment -> Sort -> [Tp] -> Sort
sortInstantiate env = instantiate []
  where
    instantiate :: [Tp] -> Sort -> [Tp] -> Sort
    instantiate substitution sort [] = sortSubstitute env (TypeSubstitution 0 substitution) sort
    instantiate substitution (SortForall sort) (tp : tps) = instantiate (tp : substitution) sort tps
    instantiate _ _ _ = error "sortInstantiate: Expected SortForall"

type RegionInstantiation = [(RegionVar, ([RegionVar], Argument RegionVar))]

-- The sort of the second argument must be the same or an instantiation of the sort of the first argument.
findArgumentSubstitution :: Argument a -> Argument a -> [(a, Argument a)]
findArgumentSubstitution argLeft argRight = substitution (argLeft, argRight) []
  where
    substitution :: (Argument a, Argument a) -> [(a, Argument a)] -> [(a, Argument a)]
    substitution (ArgumentValue a, arg) accum = (a, arg) : accum
    substitution (ArgumentList listLeft, ArgumentList listRight) accum = foldr substitution accum $ zip listLeft listRight
    substitution _ _ = error "findArgumentSubstitution: Illegal arguments"

