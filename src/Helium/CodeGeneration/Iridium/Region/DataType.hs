module Helium.CodeGeneration.Iridium.Region.DataType where

import Data.Either (lefts, rights)
import Data.List
import Data.Maybe

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Show
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Utils
import Helium.CodeGeneration.Iridium.BindingGroup
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Containment
import Helium.CodeGeneration.Iridium.Region.Utils

effectDataTypes :: TypeEnvironment -> Module -> EffectEnvironment
effectDataTypes env mod = envWithAnnotations
  where
    emptyEffectEnvironment :: EffectEnvironment
    emptyEffectEnvironment = foldr initializeDataType (EffectEnvironment emptyMap emptyMap emptyMap) datas

    envWithRegionArguments =
      writeArguments
        False
        typeRegionSort
        (\regions relation (EffectDataType annotations _ _) -> EffectDataType annotations regions $ fromMaybe [] relation)
        assignRegionArguments
        removeRecursiveRegions
        relationForDataTypes
        datas
        emptyEffectEnvironment
    
    envWithAnnotations = 
      writeArguments
        True
        (\ee tp -> typeAnnotationSortArgument ee tp [])
        (\annotations _ (EffectDataType _ regions relation) -> EffectDataType annotations regions relation)
        assignAnnotationArguments
        removeRecursiveAnnotations
        (\_ _ -> ())
        datas
        envWithRegionArguments

    relationForDataTypes :: EffectEnvironment -> [Declaration DataType] -> [RelationConstraint]
    relationForDataTypes env declarations = declarations >>= relationForDataType env

    relationForDataType :: EffectEnvironment -> Declaration DataType -> [RelationConstraint]
    relationForDataType env (Declaration _ _ _ _ (DataType constructors)) = constructors >>= relationForConstructor env

    relationForConstructor :: EffectEnvironment -> Declaration DataTypeConstructorDeclaration -> [RelationConstraint]
    relationForConstructor env (Declaration name _ _ _ (DataTypeConstructorDeclaration tp)) = concat $ zipWith (\tp arg -> containment env (tpFromType quantors tp) arg) (rights args) regionArgs
      where
        FunctionType args _ = extractFunctionTypeNoSynonyms tp
        quantors = reverse [idx | Left (Quantor idx _) <- args]
        EffectConstructor _ _ regionArgs = eeLookupConstructor env name

    datas = normalizedDataTypes env mod
    initializeDataType :: Declaration DataType -> EffectEnvironment -> EffectEnvironment
    initializeDataType (Declaration name _ _ _ (DataType constructors)) effectEnv =
      effectEnv{
        -- Assign sortUnassignedX to all data types, such that we can find recursion.
        eeDataTypes = insertMap name (EffectDataType sortUnassignedAnnotation sortUnassignedRegion []) $ eeDataTypes effectEnv,
        eeConstructors = foldr initializeConstructor (eeConstructors effectEnv) constructors
      }
    initializeConstructor :: Declaration DataTypeConstructorDeclaration -> IdMap EffectConstructor -> IdMap EffectConstructor
    initializeConstructor (Declaration name _ _ _ _) constructors = insertMap name (EffectConstructor [] [] []) constructors

sortUnassignedAnnotation :: [Sort]
sortUnassignedAnnotation = [SortPolymorphic (TypeVar (-1)) []]

sortUnassignedRegion :: [SortArgumentRegion]
sortUnassignedRegion = [SortArgumentRegionPolymorphic (TypeVar (-1)) []]

writeArguments ::
  Bool -- Should we look in function types for type dependencies
  -> (EffectEnvironment -> Tp -> Argument sort) -- Generates the argument sorts for types
  -> ([sort] -> Maybe b -> EffectDataType -> EffectDataType) -- Updates the arguments in a DataType
  -> (recursiveInfo -> [sort] -> [Argument sort] -> (Int, EffectConstructor) -> (Int, EffectConstructor)) -- Updates the arguments in a Constructor
  -> ([sort] -> ([sort], recursiveInfo)) -- Modifies sorts to remove recursive sorts, gathers info on recursive sorts
  -> (EffectEnvironment -> [Declaration DataType] -> b) -- Additional computations, used for computing the relation of the region variables
  -> [Declaration DataType]
  -> EffectEnvironment
  -> EffectEnvironment -- Resulting effect environment
writeArguments inFunctions arguments update updateCon removeRecursion additional declarations initialEnv = foldl handleGroup initialEnv groups
  where
    handleGroup :: EffectEnvironment -> BindingGroup DataType -> EffectEnvironment
    handleGroup e group = updateDataTypes sortNoRecursion (Just additionalData) e'
      where
        (_, e') = foldr updateConstructor (0, e) sorts

        -- Temp environment, used to compute additionalData
        e'' = updateDataTypes sortNoRecursion Nothing e'
        additionalData = additional e'' list
        updateDataTypes sort additionalData e = foldr (updateDataType sort additionalData) e list
        updateDataType sort additionalData (Declaration name _ _ _ _) env =
          env{ eeDataTypes = insertMapWith
            name
            (error "Region.DataType: data type not found in environment")
            (update sort additionalData)
            $ eeDataTypes env
          }
        updateConstructor (name, sort) (var, env) =
          ( var'
          , env{ eeConstructors = updateMap
              name
              con'
              $ eeConstructors env
            }
          )
          where
            con = findMap name $ eeConstructors env
            (var', con') = updateCon recursiveInfo sortNoRecursion sort (var, con)

        list :: [Declaration DataType]
        list = bindingGroupToList group
        sorts = list >>= dataTypeSort
        argumentRecursion :: [Int]
        argumentRecursion = zipWith (\_ idx -> idx) sortNoRecursion [0..]

        (sortNoRecursion, recursiveInfo) = removeRecursion $ sorts >>= (\(_, sort) -> sort >>= argumentFlatten)
        dataTypeSort (Declaration _ _ _ _ (DataType cons)) = map constructorSort cons
        constructorSort (Declaration name _ _ _ (DataTypeConstructorDeclaration tp)) = (name, map (\tp -> arguments e $ tpFromType quantors tp) $ rights args)
          where
            FunctionType args _ = extractFunctionTypeNoSynonyms tp
            quantors = reverse [idx | Left (Quantor idx _) <- args]

    groups = bindingGroups (\(DataType constructors) -> constructors >>= constructorDependencies) declarations

    constructorDependencies :: Declaration DataTypeConstructorDeclaration -> [Id]
    constructorDependencies (Declaration _ _ _ _ (DataTypeConstructorDeclaration tp))
      = concat [typeDependencies inFunctions arg | Right arg <- args]
      where
        FunctionType args _ = extractFunctionTypeNoSynonyms tp

assignRegionArguments :: () -> [SortArgumentRegion] -> [Argument SortArgumentRegion] -> (Int, EffectConstructor) -> (Int, EffectConstructor)
assignRegionArguments _ recursion args (freshInitial, EffectConstructor conAnnotation1 conAnnotation2 _) = (freshFinal, EffectConstructor conAnnotation1 conAnnotation2 conRegion)
  where
    recursion' = zipWith (\_ idx -> ArgumentValue $ variableFromIndices 1 idx) recursion [0..]
    (freshFinal, conRegion) = mapAccumL assign freshInitial args
    assign :: Int -> Argument SortArgumentRegion -> (Int, Argument RegionVar)
    assign fresh (ArgumentList [ArgumentValue (SortArgumentRegionPolymorphic (TypeVar (-1)) _)])
      -- Recursion
      = (fresh, ArgumentList $ recursion')
    assign fresh (ArgumentValue _) = (fresh + 1, ArgumentValue $ variableFromIndices 1 fresh)
    assign fresh (ArgumentList args) = ArgumentList <$> mapAccumL assign fresh args

removeRecursiveRegions :: [SortArgumentRegion] -> ([SortArgumentRegion], ())
removeRecursiveRegions args = (filter isNonRec args, ())
  where
    isNonRec (SortArgumentRegionPolymorphic (TypeVar (-1)) _) = False
    isNonRec _ = True

assignAnnotationArguments :: () -> [Sort] -> [Argument Sort] -> (Int, EffectConstructor) -> (Int, EffectConstructor)
assignAnnotationArguments _ recursion args (freshInitial, EffectConstructor _ _ conRegion) = (freshInitial, EffectConstructor ((ABottom <$) <$> args) (ABottom <$ recursion) conRegion)

removeRecursiveAnnotations :: [Sort] -> ([Sort], ())
removeRecursiveAnnotations args = (filter isNonRec args, ())
  where -- TODO: Recursion may be nested in the sort
    isNonRec (SortPolymorphic (TypeVar (-1)) _) = False
    isNonRec (SortPolymorphic _ _) = True
    isNonRec _ = False
