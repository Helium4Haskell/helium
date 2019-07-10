module Helium.CodeGeneration.Iridium.Region.EffectEnvironment where

import Data.List
import Lvm.Common.IdMap
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Relation

data EffectDataType = EffectDataType
  ![Sort] -- Annotation variables of the data type
  ![SortArgumentRegion] -- The region variables of the data type
  ![RelationConstraint]

data EffectConstructor = EffectConstructor
  -- The annotations per field of the constructor
  -- Contains functions taking the type arguments and annotation arguments of the data type and returns the annotations on the 
  ![Argument Annotation]
  -- Annotation functions taking the arguments of the constructor, returning the annotations on the data type
  ![Annotation]
  -- Instantiation of the region variables per field of the constructor
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
globalHasAdditionalRegions (EffectGlobal _ _ annotations) = case filter (/= ABottom) $ argumentFlatten annotations of
  [] -> False
  -- All annotation of a global should have the same additional arguments, so we only need to check the first one
  ALam _ (ArgumentList []) _ : _ -> False
  _ -> True

instance Show EffectEnvironment where
  show (EffectEnvironment datas constructors values)
    = "DATA TYPES\n" ++ (listFromMap datas >>= showDataType)
    ++ "\n\nCONSTRUCTORS\n" ++ (listFromMap constructors >>= showConstructor)
    ++ "\n\nGLOBALS\n" ++ (listFromMap values >>= showGlobal)
    where
      showDataType (name, EffectDataType s1 s2 constraints) = show name ++ ": " ++ show s1 ++ "; " ++ show s2 ++ "; " ++ show constraints ++ "\n"
      showConstructor (name, EffectConstructor a1 a2 a3) = show name ++ ": " ++ show a1 ++ " <=> " ++ show a2 ++ "; " ++ show a3 ++ "\n"
      showGlobal (name, EffectGlobal arity tp args) = show name ++ "[" ++ show arity ++ "]: " ++ show tp ++ "; " ++ show args ++ "\n"

typeRegionSort :: EffectEnvironment -> Tp -> Argument SortArgumentRegion
typeRegionSort env tp
  | tpIsStrict tp = ArgumentList
    [ ArgumentValue SortArgumentRegionMonomorphic -- Region for the value
    , typeRegionChildSort env (tpNotStrict tp) []
    ]
  | otherwise = ArgumentList
    [ ArgumentValue SortArgumentRegionMonomorphic -- Region for the thunk
    , ArgumentValue SortArgumentRegionMonomorphic -- Region for the value
    , typeRegionChildSort env tp []
    ]

typeRegionChildSort :: EffectEnvironment -> Tp -> [Tp] -> Argument SortArgumentRegion
typeRegionChildSort env (TpCon TConFun) _ = ArgumentList []
typeRegionChildSort env (TpStrict _) _ = error "typeRegionChildSort: Did not expect a strictness annotation on this position"
typeRegionChildSort env (TpVar tvar) tps = ArgumentValue $ SortArgumentRegionPolymorphic tvar tps
typeRegionChildSort env (TpForall tp) [] = typeRegionChildSort env tp []
typeRegionChildSort env (TpCon (TConDataType name)) tps = snd $ eeDataTypeArguments env name tps
typeRegionChildSort env (TpCon (TConTypeClassDictionary name)) tps = snd $ eeDataTypeArguments env (dictionaryDataTypeName name) tps
typeRegionChildSort env (TpCon (TConTuple _)) tps = sort
  where
    sort = ArgumentList $
      -- For each field, a region for the thunk, a region for the value and region variables for the fields / children of the element
      tps >>= (\tp -> [ArgumentValue SortArgumentRegionMonomorphic, ArgumentValue SortArgumentRegionMonomorphic, typeRegionChildSort env tp []])
typeRegionChildSort env (TpApp t1 t2) tps = typeRegionChildSort env t1 (t2 : tps)

typeAnnotationSortArgument :: EffectEnvironment -> Tp -> [Tp] -> Argument Sort
typeAnnotationSortArgument env (TpStrict tp) [] = typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TpForall tp) [] = fmap SortForall $ typeAnnotationSortArgument env tp []
typeAnnotationSortArgument env (TpVar tvar) tps = ArgumentValue $ SortPolymorphic tvar tps
typeAnnotationSortArgument env (TpCon TConFun) [tArg, tReturn] =
  fmap (SortFun annotationArg regionArg) $
    ArgumentList
      [ ArgumentValue
        $ SortFun argumentEmpty (ArgumentValue SortArgumentRegionMonomorphic)
        $ SortFun argumentEmpty regionReturn SortRelation
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
  TConTuple _ -> ArgumentList $ map (\tp -> typeAnnotationSortArgument env tp []) tps

eeDataTypeArguments :: EffectEnvironment -> Id -> [Tp] -> (Argument Sort, Argument SortArgumentRegion)
eeDataTypeArguments env name [] =
  -- Fast variant, if the data type does not have type arguments then we do not have to perform a substitution
  (ArgumentList $ fmap ArgumentValue annotationSort, ArgumentList $ fmap ArgumentValue regionSort)
  where
    (EffectDataType annotationSort regionSort _) = eeLookupDataType env name
eeDataTypeArguments env name types =
  ( instantiateArgumentTypes env types $ ArgumentList $ fmap ArgumentValue annotationSort
  , instantiateArgumentTypes env types $ ArgumentList $ fmap ArgumentValue regionSort
  )
  where
    (EffectDataType annotationSort regionSort _) = eeLookupDataType env name

class Instantiatable a where
  instantiateType' :: EffectEnvironment -> TypeInstantiation -> a -> Argument a

instantiateType :: Instantiatable a => EffectEnvironment -> Tp -> a -> Argument a
instantiateType env tp = instantiateType' env (TypeInstantiation 0 tp)

instantiateArgumentTypes :: Instantiatable a => EffectEnvironment -> [Tp] -> Argument a -> Argument a
instantiateArgumentTypes env tps arg = foldr (instantiateArgumentType env) arg tps

instantiateArgumentType :: Instantiatable a => EffectEnvironment -> Tp -> Argument a -> Argument a
instantiateArgumentType env tp = instantiateArgumentType' env (TypeInstantiation 0 tp)

instantiateArgumentType' :: Instantiatable a => EffectEnvironment -> TypeInstantiation -> Argument a -> Argument a
instantiateArgumentType' env subst arg = arg >>= instantiateType' env subst

instance Instantiatable SortArgumentRegion where
  instantiateType' env subst (SortArgumentRegionPolymorphic tvar tps) = case typeInstantiationTry subst tvar of
    Left tvar' -> ArgumentValue $ SortArgumentRegionPolymorphic tvar' tps'
    Right tp -> typeRegionChildSort env tp tps'
    where
      tps' = tpInstantiate' subst <$> tps
  instantiateType' _ _ arg = ArgumentValue arg

instance Instantiatable Sort where
  instantiateType' env subst (SortForall s) = SortForall <$> instantiateType' env (typeInstantiationIncrement subst) s
  instantiateType' env subst (SortFun argA argR s) = SortFun argA' argR' <$> instantiateType' env subst s
    where
      argA' = instantiateArgumentType' env subst argA
      argR' = instantiateArgumentType' env subst argR
  instantiateType' env subst (SortPolymorphic tvar tps) = case typeInstantiationTry subst tvar of
    Left tvar' -> ArgumentValue $ SortPolymorphic tvar' tps'
    Right tp -> typeAnnotationSortArgument env tp tps'
    where
      tps' = tpInstantiate' subst <$> tps
  instantiateType' env subst s = ArgumentValue s

type RegionInstantiation = [(RegionVar, ([RegionVar], Argument RegionVar))]

-- The sort of the second argument must be the same or an instantiation of the sort of the first argument.
findArgumentSubstitution :: Argument a -> Argument a -> [(a, Argument a)]
findArgumentSubstitution argLeft argRight = substitution (argLeft, argRight) []
  where
    substitution :: (Argument a, Argument a) -> [(a, Argument a)] -> [(a, Argument a)]
    substitution (ArgumentValue a, arg) accum = (a, arg) : accum
    substitution (ArgumentList listLeft, ArgumentList listRight) accum = foldr substitution accum $ zip listLeft listRight
    substitution _ _ = error "findArgumentSubstitution: Illegal arguments"
