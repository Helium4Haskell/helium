module Helium.CodeGeneration.Iridium.Region.DataType (ConstructorEnv, ConstructorAnnotation(..), createDataTypeEnv) where

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet

import Data.List
import Data.Either
import qualified Data.IntMap.Strict as IntMap

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.TypeEnvironment
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Containment
import Helium.CodeGeneration.Iridium.Region.Utils

import Debug.Trace

type ConstructorEnv = IdMap ConstructorAnnotation
data ConstructorAnnotation = ConstructorAnnotation
  { constructorEffectConstruct :: !Annotation
  , constructorReturnConstruct :: !Annotation
  , constructorEffectDestruct :: !Annotation
  , constructorReturnDestruct :: ![Annotation]
  }

instance Show ConstructorAnnotation where
  show (ConstructorAnnotation effectConstruct returnConstruct effectDestruct returnDestruct) =
    unlines $ ["Effect construct", show effectConstruct, "Return construct", show returnConstruct, "Effect destruct", show effectDestruct, "Return destruct"]
      ++ map show returnDestruct

createDataTypeEnv :: TypeEnvironment -> [Declaration DataType] -> (DataTypeEnv, ConstructorEnv)
createDataTypeEnv env dataTypes = assignAnnotations env dataTypes $ createDataTypeEnvRegions env dataTypes

createDataTypeEnvRegions :: TypeEnvironment -> [Declaration DataType] -> (DataTypeEnv, ConstructorEnv)
createDataTypeEnvRegions env dataTypes = foldl' (flip assignGroup) (emptyMap, emptyMap) groups
  where
    groups = bindingGroups (dataTypeDependencies False) dataTypes

    assignGroup :: BindingGroup DataType -> (DataTypeEnv, ConstructorEnv) -> (DataTypeEnv, ConstructorEnv)
    assignGroup (BindingNonRecursive decl@(Declaration dataTypeName _ _ _ dataType)) (dataTypeEnv, constructorEnv) = -- trace ("NonRecursive " ++ show dataTypeName ++ "\n" ++ show (zip constructorNames $ zipWith createConstructor regionSorts regionVarsPerField))
      ( insertMap dataTypeName dataTypeSort dataTypeEnv
      , foldl' (flip $ uncurry insertMap) constructorEnv (zip constructorNames $ zipWith createConstructor regionSorts regionVarsPerField)
      )
      -- Assign region variables to a non-recursive data type by making a tuple (over the constructors)
      -- of tuples (over the fields).
      where
        constructors = getConstructors decl
        constructorNames = map (\(DataTypeConstructor name _) -> name) constructors

        dataTypeSort :: DataTypeSort
        dataTypeSort = DataTypeSort containmentRelation SortUnit regionSort

        containmentRelation = mconcat $ concat $ zipWith (zipWith $ containment' dataTypeEnv) types regionVarsPerField

        quantors = case constructors of
          [] -> []
          DataTypeConstructor _ tp : _ -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in lefts args

        types :: [[Type]]
        types = map (\(DataTypeConstructor _ tp) -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in map (typeNormalize env) $ rights args) constructors

        regionSorts :: [[RegionSort]]
        regionSorts = map (regionSortOfType dataTypeEnv) <$> types

        regionSort :: RegionSort
        regionSort
          = flip (foldr RegionSortForall) quantors
          $ RegionSortTuple $ map RegionSortTuple regionSorts

        regionVars :: RegionVars
        regionVars = regionSortToVars 0 regionSort

        regionVarsPerField :: [[RegionVars]]
        regionVarsPerField = untuple <$> untuple regionVars

        untuple (RegionVarsTuple vars) = vars
        untuple _ = error "createDataTypeEnvRegions: Expected RegionVarsTuple"

        createConstructor :: [RegionSort] -> [RegionVars] -> ConstructorAnnotation
        createConstructor rs rvars = ConstructorAnnotation (effect True) (ABottom SortRelation) (effect False) []
          where
            size = sum $ map regionSortSize rs

            effect :: Bool -> Annotation
            effect construct
              = flip (foldr AForall) quantors
              $ ALam SortUnit (skipRegionSortForalls regionSort) lc1
              $ flip (foldr $ \s -> ALam SortUnit s lc2) rs
              $ arelation
              $ relationFromConstraints
              $ zipFlattenRegionVars f (mapRegionVars (weakenRegionVar 0 size) $ RegionVarsTuple rvars)
              $ regionSortToVars 0 $ RegionSortTuple rs
              where
                (lc1, lc2, f)
                  | construct = (LifetimeContextLocalBottom, LifetimeContextAny, flip Outlives)
                  | otherwise = (LifetimeContextAny, LifetimeContextLocalBottom, Outlives)
    assignGroup (BindingRecursive decls) (dataTypeEnv, constructorEnv)
      | not $ dataTypesPolymorphicRecursion decls = -- trace ("Recursive, no polymorphic recursion: " ++ (decls >>= (show . declarationName)))
        ( dataTypeEnv1
        , foldl' (flip $ uncurry insertMap) constructorEnv 
          $ concat
          $ zipWith3 assignDataType decls types regionVarsPerField
        )
      where
        -- Create an environment where the current data types have region sort ().
        -- This way we can gather all other region variables for the datatypes, except for the recursive positions.
        -- The region arguments of recursive positions will be instantiated with the same regions.
        dataTypeEnvUnit
          = foldl' (flip $ uncurry insertMap) dataTypeEnv
          $ map (\decl -> (declarationName decl, DataTypeSort relationEmpty SortUnit regionSortUnit)) decls

        regionSortUnit :: RegionSort
        regionSortUnit = flip (foldr RegionSortForall) quantors RegionSortUnit

        quantors = case decls >>= getConstructors of
          [] -> []
          DataTypeConstructor _ tp : _ -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in lefts args


        -- For each data type, for each constructor, for each field, the type
        types :: [[[Type]]]
        types = map
          (\(Declaration _ _ _ _ (DataType constructors)) ->
            map
              (\(Declaration _ _ _ _ (DataTypeConstructorDeclaration tp _)) -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in map (typeNormalize env) $ rights args)
              constructors
          )
          decls

        -- Region sorts of all fields. Recursive positions get sort ().
        regionSortsWithoutRecursion :: [[[RegionSort]]]
        regionSortsWithoutRecursion = map (map $ map $ regionSortOfType dataTypeEnvUnit) types

        regionSort :: RegionSort
        regionSort
          = flip (foldr RegionSortForall) quantors
          $ RegionSortTuple $ map (RegionSortTuple . map RegionSortTuple) regionSortsWithoutRecursion

        dataTypeEnv1
          = foldl' (flip $ uncurry insertMap) dataTypeEnv
          $ map (\decl -> (declarationName decl, DataTypeSort relationEmpty SortUnit regionSort)) decls

        regionVars :: RegionVars
        regionVars = regionSortToVars 0 regionSort

        regionVarsPerField :: [[[RegionVars]]]
        regionVarsPerField = map (map untuple . untuple) $ untuple regionVars

        untuple (RegionVarsTuple vars) = vars
        untuple _ = error "createDataTypeEnvRegions: Expected RegionVarsTuple"

        assignDataType :: Declaration DataType -> [[Type]] -> [[RegionVars]] -> [(Id, ConstructorAnnotation)]
        assignDataType (Declaration _ _ _ _ (DataType cs)) tps vars = zipWith3 assignConstructor cs tps vars

        assignConstructor :: Declaration DataTypeConstructorDeclaration -> [Type] -> [RegionVars] -> (Id, ConstructorAnnotation)
        assignConstructor (Declaration name _ _ _ _) fields vars =
          ( name
          , ConstructorAnnotation (effect True) (ABottom SortRelation) (effect False) []
          )
          where
            fieldSort = regionSortOfType dataTypeEnv1 <$> fields
            fieldVars = regionSortToVars 0 (RegionSortTuple fieldSort)

            vars' = mapRegionVars (weakenRegionVar 0 (regionVarsSize fieldVars)) <$> vars

            effect :: Bool -> Annotation
            effect construct
              = flip (foldr AForall) quantors
              $ ALam SortUnit (skipRegionSortForalls regionSort) lc1
              $ flip (foldr $ \s -> ALam SortUnit s lc2) fieldSort
              $ arelation
              $ relationFromConstraints
              $ zipFlattenRec f (mapRegionVars (weakenRegionVar 0 (regionVarsSize fieldVars)) regionVars) (RegionVarsTuple vars') fieldVars
              where
                (lc1, lc2, f)
                  | construct = (LifetimeContextLocalBottom, LifetimeContextAny, flip Outlives)
                  | otherwise = (LifetimeContextAny, LifetimeContextLocalBottom, Outlives)

    assignGroup (BindingRecursive decls) (dataTypeEnv, constructorEnv) = -- trace ("Recursive, with polymorphic recursion: " ++ (decls >>= (show . declarationName)))
      -- Fallback, assign one region argument to each data type for all recursive positions.
      ( dataTypeEnv1
      , foldl' (flip $ uncurry insertMap) constructorEnv (decls >>= assignDataType)
      )
      where
        dataTypeEnv1
          = foldl' (flip $ uncurry insertMap) dataTypeEnv
          $ map (\decl -> (declarationName decl, DataTypeSort relationEmpty SortUnit $ regionSort $ declarationValue decl)) decls

        regionSort :: DataType -> RegionSort
        regionSort dataType = flip (foldr RegionSortForall) (dataTypeQuantors dataType) RegionSortMonomorphic

        assignDataType :: Declaration DataType -> [(Id, ConstructorAnnotation)]
        assignDataType (Declaration _ _ _ _ (DataType constructors)) = assignConstructor <$> constructors

        assignConstructor :: Declaration DataTypeConstructorDeclaration -> (Id, ConstructorAnnotation)
        assignConstructor (Declaration name _ _ _ (DataTypeConstructorDeclaration tp _)) =
          ( name
          , ConstructorAnnotation (effect True) (ABottom SortRelation) (effect False) []
          )
          where
            FunctionType args _ = extractFunctionTypeNoSynonyms tp

            quantors = lefts args
            fields = typeNormalize env <$> rights args

            rs = regionSortOfType dataTypeEnv1 <$> fields

            effect :: Bool -> Annotation
            effect construct
              = flip (foldr AForall) quantors
              $ ALam SortUnit RegionSortMonomorphic lc1
              $ flip (foldr $ \s -> ALam SortUnit s lc2) rs
              $ arelation
              $ relationFromConstraints
              $ map (f $ RegionLocal $ regionVarsSize vars)
              $ flattenRegionVars vars
              where
                vars = regionSortToVars 0 $ RegionSortTuple rs
                (lc1, lc2, f)
                  | construct = (LifetimeContextLocalBottom, LifetimeContextAny, flip Outlives)
                  | otherwise = (LifetimeContextAny, LifetimeContextLocalBottom, Outlives)

dataTypeDependencies :: Bool -> DataType -> [Id]
dataTypeDependencies inFunctions (DataType constructors) = constructors >>= (\(Declaration _ _ _ _ (DataTypeConstructorDeclaration tp _)) -> functionDependencies tp)
  where
    functionDependencies :: Type -> [Id]
    functionDependencies tp =
      let
        FunctionType args _ = extractFunctionTypeNoSynonyms tp
      in
        rights args >>= typeDependencies inFunctions

-- Checks whether the data types have polymorphic recursion
dataTypesPolymorphicRecursion :: [Declaration DataType] -> Bool
dataTypesPolymorphicRecursion dataTypes
  | [] <- constructors = True
  | FunctionType args1 _ : rest <- constructors
    -- Return true if any constructor has a different number of type arguments
    = any (\(FunctionType args2 _) -> length (lefts args1) /= length (lefts args2)) rest
    -- or if the type arguments are instantiated differently
    || any (\(FunctionType args2 _) -> any (isPolymorphicRecursive 0 $ length $ lefts args1) $ rights args2) constructors
  where
    group = setFromList $ map declarationName dataTypes

    constructors :: [FunctionType]
    constructors = [ extractFunctionTypeNoSynonyms tp | Declaration _ _ _ _ (DataType cs) <- dataTypes, Declaration _ _ _ _ (DataTypeConstructorDeclaration tp _) <- cs ]

    isPolymorphicRecursive :: Int -> Int -> Type -> Bool
    isPolymorphicRecursive first count tp = checkAp 0 tp
      where
        check = isPolymorphicRecursive first count

        checkAp :: Int -> Type -> Bool
        checkAp idx (TAp t1 (TVar tvar))
          | tvar == first + idx = checkAp (idx + 1) t1
        checkAp _ (TAp t1 t2) = checkApExternal t1 || check t2
        checkAp idx (TStrict t1) = checkAp idx t1
        checkAp idx (TForall _ _ t1) = check t1
        checkAp idx (TVar _) = False
        checkAp idx (TCon con) = case con of
          TConDataType name
            | name `elemSet` group -> idx /= count -- Check whether the type was saturated. If not, this is polymorphic recursion.
            | otherwise -> False
          TConTypeClassDictionary name -> checkAp idx $ TCon $ TConTypeClassDictionary $ dictionaryDataTypeName name
          _ -> False

        -- Checks a type, assuming that it is not (an instantiation of a) data type from this binding group.
        -- If it appears to be such data type, it will return True, as this will then be a form of polymorphic
        -- recursion.
        checkApExternal :: Type -> Bool
        checkApExternal (TAp t1 t2) = checkApExternal t1 || check t2
        checkApExternal (TStrict t1) = checkApExternal t1
        checkApExternal (TForall _ _ t1) = check t1
        checkApExternal (TVar _) = False
        checkApExternal (TCon con) = case con of
          TConDataType name -> name `elemSet` group
          TConTypeClassDictionary name -> checkApExternal $ TCon $ TConTypeClassDictionary $ dictionaryDataTypeName name
          _ -> False

-- Replaces a () on the left argument with 'recursive', for recursive fields of the datatype.
zipFlattenRec :: (RegionVar -> RegionVar -> a) -> RegionVars -> RegionVars -> RegionVars -> [a]
zipFlattenRec f recursive varsLeft varsRight = go varsLeft varsRight []
  where
    go (RegionVarsSingle x) (RegionVarsSingle y) = (f x y :)
    go (RegionVarsTuple []) (RegionVarsTuple []) = id
    go (RegionVarsTuple []) ys = (zipFlattenRegionVars f recursive ys ++)
    go (RegionVarsTuple xs) (RegionVarsTuple ys) = goList xs ys

    goList [] [] = id
    goList (v:vs) (v':vs') = go v v' . goList vs vs'
    goList _ _ = error "zipFlattenRec: Region vars mismatch"

skipRegionSortForalls :: RegionSort -> RegionSort
skipRegionSortForalls (RegionSortForall _ rs) = skipRegionSortForalls rs
skipRegionSortForalls rs = rs

addConstructorAnnotations :: ConstructorEnv -> [(Id, Annotation, [Annotation])] -> ConstructorEnv
addConstructorAnnotations = foldl' f
  where
    f env (name, a, as) = updateMapWith name (\c -> c{ constructorReturnConstruct = a, constructorReturnDestruct = as }) env

assignAnnotations :: TypeEnvironment -> [Declaration DataType] -> (DataTypeEnv, ConstructorEnv) -> (DataTypeEnv, ConstructorEnv)
assignAnnotations env dataTypes = flip (foldl' (flip assignGroup)) groups
  where
    groups = bindingGroups (dataTypeDependencies True) dataTypes

    assignGroup :: BindingGroup DataType -> (DataTypeEnv, ConstructorEnv) -> (DataTypeEnv, ConstructorEnv)
    assignGroup (BindingNonRecursive decl@(Declaration dataTypeName _ _ _ dataType)) (dataTypeEnv, constructorEnv) =
      ( updateMapWith dataTypeName (\(DataTypeSort cr _ rs) -> DataTypeSort cr annotationSort rs) dataTypeEnv
      , addConstructorAnnotations constructorEnv $ zipWith3 assignConstructor constructorNames [0..] sorts
      )
      -- Assign annotation variables to a non-recursive data type by making a tuple (over the constructors)
      -- of tuples (over the fields).
      where
        constructors = getConstructors decl
        constructorNames = map (\(DataTypeConstructor name _) -> name) constructors

        quantors = case constructors of
          [] -> []
          DataTypeConstructor _ tp : _ -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in lefts args

        types :: [[Type]]
        types = map (\(DataTypeConstructor _ tp) -> let FunctionType args _ = extractFunctionTypeNoSynonyms tp in map (typeNormalize env) $ rights args) constructors

        sorts :: [[Sort]]
        sorts = map (sortOfType dataTypeEnv) <$> types

        annotationSort :: Sort
        annotationSort
          = foldr SortForall annotationSort' quantors

        annotationSort' :: Sort
        annotationSort'
          = SortTuple $ map SortTuple sorts

        assignConstructor :: Id -> Int -> [Sort] -> (Id, Annotation, [Annotation])
        assignConstructor name constructorIndex fields =
          ( name
          , flip (foldr AForall) quantors
              $ flip (foldr $ \s -> ALam s RegionSortUnit LifetimeContextAny) fields
              $ ATuple
              $ zipWith
                  (\sorts' idx -> if idx == constructorIndex then ATuple $ map (AVar . AnnotationVar) vars else ABottom (SortTuple sorts'))
                  sorts
                  [0..]
          , map f [0 .. count - 1]
          )
          where
            count = length fields
            vars = [count - 1, count - 2 .. 0]

            f fieldIndex =
              flip (foldr AForall) quantors
              $ ALam annotationSort RegionSortUnit LifetimeContextAny
              $ AProject (AProject (AVar $ AnnotationVar 0) constructorIndex) fieldIndex
    assignGroup (BindingRecursive decls) (dataTypeEnv, constructorEnv) =
      -- Fallback, don't store annotations and default to top
      ( dataTypeEnv1
      , addConstructorAnnotations constructorEnv $ decls >>= assignDataType
      )
      where
        dataTypeEnv1 = foldl'
          (\e decl -> updateMapWith (declarationName decl) (\(DataTypeSort cr _ rs) -> DataTypeSort cr (annotationSort $ declarationValue decl) rs) e)
          dataTypeEnv
          decls

        annotationSort :: DataType -> Sort
        annotationSort dataType = flip (foldr SortForall) (dataTypeQuantors dataType) SortUnit

        assignDataType :: Declaration DataType -> [(Id, Annotation, [Annotation])]
        assignDataType (Declaration _ _ _ _ (DataType constructors)) = assignConstructor <$> constructors

        assignConstructor :: Declaration DataTypeConstructorDeclaration -> (Id, Annotation, [Annotation])
        assignConstructor (Declaration name _ _ _ (DataTypeConstructorDeclaration tp _)) =
          ( name
          , flip (foldr AForall) quantors
              $ flip (foldr $ \s -> ALam s RegionSortUnit LifetimeContextAny) sorts
              $ ATuple []
          , map f sorts
          )
          where
            FunctionType args _ = extractFunctionTypeNoSynonyms tp

            quantors = lefts args
            fields = typeNormalize env <$> rights args

            sorts = sortOfType dataTypeEnv1 <$> fields

            f s =
              flip (foldr AForall) quantors
              $ ALam SortUnit RegionSortUnit LifetimeContextAny
              $ ATop s
