module Helium.CodeGeneration.Iridium.Region.EffectEnvironment where

import Data.List
import Lvm.Common.IdMap
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Relation

data EffectDataType = EffectDataType
  ![TypeVar]
  !(SortArgument Sort) -- Annotation variables of the data type
  !(SortArgument SortArgumentRegion) -- The region variables of the data type
  ![RelationConstraint]

data EffectConstructor = EffectConstructor
  ![Argument AnnotationVar] -- Instantiation of the region and annotation variables per field of the constructor
  ![Argument RegionVar]

data EffectGlobal = EffectGlobal !(Argument Annotation)

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

instance Show EffectEnvironment where
  show (EffectEnvironment datas constructors values)
    = "DATA TYPES\n" ++ (listFromMap datas >>= showDataType)
    ++ "\n\nCONSTRUCTORS\n" ++ (listFromMap constructors >>= showConstructor)
    ++ "\n\nGLOBALS\n" ++ (listFromMap values >>= showGlobal)
    where
      showDataType (name, EffectDataType args s1 s2 constraints) = show name ++ (args >>= (\arg -> " " ++ show arg)) ++ ": " ++ show s1 ++ "; " ++ show s2 ++ "; " ++ show constraints ++ "\n"
      showConstructor (name, EffectConstructor a1 a2) = show name ++ ": " ++ show a1 ++ "; " ++ show a2 ++ "\n"
      showGlobal (name, EffectGlobal args) = show name ++ ": " ++ show args ++ "\n"

typeRegionSort :: EffectEnvironment -> Type -> SortArgument SortArgumentRegion
typeRegionSort env tp
  | typeIsStrict tp = SortArgumentList
    [ SortArgumentMonomorphic SortArgumentRegion -- Region for the value
    , typeRegionChildSort env (typeNotStrict tp) []
    ]
  | otherwise = SortArgumentList
    [ SortArgumentMonomorphic SortArgumentRegion -- Region for the thunk
    , SortArgumentMonomorphic SortArgumentRegion -- Region for the value
    , typeRegionChildSort env tp []
    ]

typeRegionChildSort :: EffectEnvironment -> Type -> [Type] -> SortArgument SortArgumentRegion
typeRegionChildSort env (TCon TConFun) _ = SortArgumentList []
typeRegionChildSort env (TStrict _) _ = error "typeRegionChildSort: Did not expect a strictness annotation on this position"
typeRegionChildSort env (TVar tvar) tps = SortArgumentPolymorphic (TypeVar tvar) tps
typeRegionChildSort env (TForall (Quantor tvar _) _ tp) [] = typeRegionChildSort env tp []
typeRegionChildSort env (TCon (TConDataType name)) tps = snd $ eeDataTypeArguments env name tps
typeRegionChildSort env (TCon (TConTypeClassDictionary name)) tps = snd $ eeDataTypeArguments env (dictionaryDataTypeName name) tps
typeRegionChildSort env (TCon (TConTuple _)) tps = sort
  where
    sort = SortArgumentList $
      -- For each field, a region for the thunk, a region for the value and region variables for the fields / children of the element
      tps >>= (\tp -> [SortArgumentMonomorphic SortArgumentRegion, SortArgumentMonomorphic SortArgumentRegion, typeRegionChildSort env tp []])
typeRegionChildSort env (TAp t1 t2) tps = typeRegionChildSort env t1 (t2 : tps)

typeAnnotationSortArgument :: EffectEnvironment -> Type -> [Type] -> SortArgument Sort
typeAnnotationSortArgument env (TStrict tp) [] = typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TForall (Quantor tvar _) _ tp) [] = fmap (SortForall (TypeVar tvar)) $ typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TVar tvar) tps = SortArgumentPolymorphic (TypeVar tvar) tps
typeAnnotationSortArgument env (TCon TConFun) [tArg, tReturn] =
  SortArgumentList
    [ SortArgumentMonomorphic
      $ SortFun annotationArg regionArg $ SortFun sortArgumentEmpty regionReturn SortRelation
    , fmap (SortFun annotationArg regionArg) annotationReturn
    ]
  where
    regionArg = typeRegionSort env tArg
    annotationArg = typeAnnotationSortArgument env tArg []
    regionReturn = typeRegionSort env (typeToStrict tReturn)
    annotationReturn = typeAnnotationSortArgument env tReturn []
typeAnnotationSortArgument env (TAp t1 t2) tps = typeAnnotationSortArgument env t1 (t2 : tps)
typeAnnotationSortArgument env (TCon con) tps = case con of
  TConFun -> error "typeAnnotationSortArgument: Expected a type of kind *"
  TConDataType name -> fst $ eeDataTypeArguments env name tps
  TConTypeClassDictionary name -> fst $ eeDataTypeArguments env (dictionaryDataTypeName name) tps
  TConTuple _ -> SortArgumentList $ map (\tp -> typeAnnotationSortArgument env tp []) tps

eeDataTypeArguments :: EffectEnvironment -> Id -> [Type] -> (SortArgument Sort, SortArgument SortArgumentRegion)
eeDataTypeArguments env name [] =
  -- Fast variant, if the data type does not have type arguments then we do not have to perform a substitution
  (annotationSort, regionSort)
  where
    (EffectDataType _ annotationSort regionSort _) = eeLookupDataType env name
eeDataTypeArguments env name types =
  ( sortArgumentAnnotationSubstitute env substitution annotationSort
  , sortArgumentRegionSubstitute env substitution regionSort
  )
  where
    (EffectDataType tvars annotationSort regionSort _) = eeLookupDataType env name
    substitution = zip tvars types

type Substitution = [(TypeVar, Type)]

sortArgumentRegionSubstitute :: EffectEnvironment -> Substitution -> SortArgument SortArgumentRegion -> SortArgument SortArgumentRegion
sortArgumentRegionSubstitute env substitution = sortArgumentSubstitute fns id
  where
    fns = map f substitution
    f (tvar, tp) = (tvar, typeRegionChildSort env tp)

sortArgumentAnnotationSubstitute :: EffectEnvironment -> Substitution -> SortArgument Sort -> SortArgument Sort
sortArgumentAnnotationSubstitute env substitution = sortArgumentSubstitute fns (sortSubstitute env substitution)
  where
    fns = map f substitution
    f (tvar, tp) = (tvar, typeAnnotationSortArgument env tp)

sortSubstitute :: EffectEnvironment -> Substitution -> Sort -> Sort
sortSubstitute env substitution SortRelation = SortRelation
sortSubstitute env substitution (SortForall tvar sort)
  | null substitution' = SortForall tvar sort
  | otherwise = SortForall tvar $ sortSubstitute env substitution' sort
  where
    substitution' = filter ((tvar /=) . fst) substitution
sortSubstitute env substitution (SortFun argumentAnnotation argumentRegion sort) = SortFun argumentAnnotation' argumentRegion' sort'
  where
    argumentAnnotation' = sortArgumentAnnotationSubstitute env substitution argumentAnnotation
    argumentRegion' = sortArgumentRegionSubstitute env substitution argumentRegion
    sort' = sortSubstitute env substitution sort

sortInstantiate :: EffectEnvironment -> Sort -> [Type] -> Sort
sortInstantiate env = instantiate []
  where
    instantiate :: Substitution -> Sort -> [Type] -> Sort
    instantiate substitution sort [] = sortSubstitute env substitution sort
    instantiate substitution (SortForall tvar sort) (tp : tps) = instantiate ((tvar, tp) : substitution) sort tps
    instantiate _ _ _ = error "sortInstantiate: Expected SortForall"

type RegionInstantiation = [(RegionVar, ([RegionVar], Argument RegionVar))]

annotationSubstitute' :: EffectEnvironment -> Substitution -> RegionInstantiation -> [AnnotationVar] -> [RegionVar] -> Annotation -> ([AnnotationVar], [RegionVar], Annotation)
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion (AForall tvar annotation)
  = (freshAnnotation', freshRegion', AForall tvar annotation')
  where
    substitution' = filter ((tvar /=) . fst) substitution
    (freshAnnotation', freshRegion', annotation') = annotationSubstitute' env substitution' regionInstantiation freshAnnotation freshRegion annotation
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion (ALam paramAnnotation paramRegion annotation)
  = (freshAnnotation'', freshRegion'', ALam paramAnnotation' paramRegion' annotation')
  where
    (freshAnnotation', paramAnnotation') = parameterAnnotationSubstitute env substitution freshAnnotation paramAnnotation
    (freshRegion', regionInstantiation', paramRegion') = parameterRegionSubstitute env substitution freshRegion regionInstantiation paramRegion
    (freshAnnotation'', freshRegion'', annotation') = annotationSubstitute' env substitution (regionInstantiation') freshAnnotation' freshRegion' annotation
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion (AApp annotation argAnnotation argRegion)
  = (freshAnnotation'', freshRegion'', AApp annotation' argAnnotation' argRegion')
  where
    (freshAnnotation', freshRegion', argAnnotation') = argumentAnnotationSubstitute env substitution regionInstantiation freshAnnotation freshRegion argAnnotation
    argRegion' = argumentRegionSubstitute regionInstantiation argRegion
    (freshAnnotation'', freshRegion'', annotation') = annotationSubstitute' env substitution regionInstantiation freshAnnotation' freshRegion' annotation
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion (ARelation constraints) = (freshAnnotation, freshRegion, ARelation constraints')
  where
    constraints' = instantiateRelationConstraints (\r -> fmap fst $ lookup r regionInstantiation) constraints
    instantiateRegion r2 = case lookup r2 regionInstantiation of
      Nothing -> error "annotationSubstitute: right operand of a constraint should be polymorphic on the same type as the left operand."
      Just (rs2, _) -> rs2
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion (AJoin a1 a2)
  = (freshAnnotation'', freshRegion'', AJoin a1' a2')
  where
    (freshAnnotation', freshRegion', a1') = annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion a1
    (freshAnnotation'', freshRegion'', a2') = annotationSubstitute' env substitution regionInstantiation freshAnnotation' freshRegion' a2
-- AVar, AThunk: No need to substitute
annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion annotation = (freshAnnotation, freshRegion, annotation)

parameterAnnotationSubstitute :: EffectEnvironment -> Substitution -> [AnnotationVar] -> Parameter AnnotationVar Sort -> ([AnnotationVar], Parameter AnnotationVar Sort)
parameterAnnotationSubstitute env substitution freshAnnotation (ParameterMonomorphic var sort)
  = (freshAnnotation, ParameterMonomorphic var $ sortSubstitute env substitution sort)
parameterAnnotationSubstitute env substitution freshAnnotation (ParameterPolymorphic var tvar tps) = case lookup tvar substitution of 
  Nothing -> (freshAnnotation, ParameterPolymorphic var tvar tps')
  Just tp -> sortArgumentToParameter freshAnnotation $ typeAnnotationSortArgument env tp tps'
  where
    tps' = map (typeNormalize typeEnvEmpty . typeSubstitutions substitution') tps
    substitution' = map (\(TypeVar idx, tp) -> (idx, tp)) substitution
parameterAnnotationSubstitute env substitution freshAnnotation (ParameterList params)
  = fmap ParameterList $ mapAccumL (parameterAnnotationSubstitute env substitution) freshAnnotation params

parameterRegionSubstitute :: EffectEnvironment -> Substitution -> [RegionVar] -> RegionInstantiation -> Parameter RegionVar SortArgumentRegion -> ([RegionVar], RegionInstantiation, Parameter RegionVar SortArgumentRegion)
parameterRegionSubstitute env substitution freshRegion regionInstantiationAccum (ParameterPolymorphic regionVar tvar tps) = case lookup tvar substitution of
  Nothing -> (freshRegion, regionInstantiationAccum, ParameterPolymorphic regionVar tvar tps')
  Just tp ->
    let
      sort = typeRegionChildSort env tp tps'
      param :: Parameter RegionVar SortArgumentRegion
      (freshRegion', param) = sortArgumentToParameter freshRegion sort
      paramList :: [RegionVar]
      paramList = parameterNames param
      instantiation :: (RegionVar, ([RegionVar], Argument RegionVar))
      instantiation = (regionVar, (paramList, parameterToArgument param))
    in (freshRegion', instantiation : regionInstantiationAccum, param)
  where
    tps' = map (typeNormalize typeEnvEmpty . typeSubstitutions substitution') tps
    substitution' = map (\(TypeVar idx, tp) -> (idx, tp)) substitution
parameterRegionSubstitute env substitution freshRegion regionInstantiationAccum (ParameterList params)
  = (freshRegion', regionInstantiationAccum', ParameterList params')
  where
    ((freshRegion', regionInstantiationAccum'), params') = mapAccumL f (freshRegion, regionInstantiationAccum) params
    f (freshR, regionI) param =
      let (freshR', regionI', param') = parameterRegionSubstitute env substitution freshR regionI param
      in ((freshR', regionI'), param')
-- Monomorphic parameter
parameterRegionSubstitute env substitution freshRegion regionInstantiationAccum param = (freshRegion, regionInstantiationAccum, param)

argumentAnnotationSubstitute :: EffectEnvironment -> Substitution -> RegionInstantiation -> [AnnotationVar] -> [RegionVar] -> Argument Annotation -> ([AnnotationVar], [RegionVar], Argument Annotation)
argumentAnnotationSubstitute env substitution regionInstantiation freshAnnotation freshRegion (ArgumentValue annotation)
  = (freshAnnotation', freshRegion', ArgumentValue annotation')
  where
    (freshAnnotation', freshRegion', annotation') = annotationSubstitute' env substitution regionInstantiation freshAnnotation freshRegion annotation
argumentAnnotationSubstitute env substitution regionInstantiation freshAnnotation freshRegion (ArgumentList args)
  = (freshAnnotation', freshRegion', ArgumentList args')
  where
    ((freshAnnotation', freshRegion'), args') = mapAccumL f (freshAnnotation, freshRegion) args
    f (freshA, freshR) arg = ((freshA', freshR'), arg')
      where
        (freshA', freshR', arg') = argumentAnnotationSubstitute env substitution regionInstantiation freshA freshR arg

argumentRegionSubstitute :: RegionInstantiation -> Argument RegionVar -> Argument RegionVar
argumentRegionSubstitute regionInstantiation (ArgumentValue var) = case lookup var regionInstantiation of
  Nothing -> ArgumentValue var
  Just (_, args) -> args

-- The sort of the second argument must be the same or an instantiation of the sort of the first argument.
findArgumentSubstitution :: Argument a -> Argument a -> [(a, Argument a)]
findArgumentSubstitution argLeft argRight = substitution (argLeft, argRight) []
  where
    substitution :: (Argument a, Argument a) -> [(a, Argument a)] -> [(a, Argument a)]
    substitution (ArgumentValue a, arg) accum = (a, arg) : accum
    substitution (ArgumentList listLeft, ArgumentList listRight) accum = foldr substitution accum $ zip listLeft listRight
    substitution _ _ = error "findArgumentSubstitution: Illegal arguments"

