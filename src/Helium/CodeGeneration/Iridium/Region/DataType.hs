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
        (variableFromIndices 0)
        typeRegionSort
        (\regions relation (EffectDataType annotations _ _) -> EffectDataType annotations regions $ fromMaybe [] relation)
        (\regions (EffectConstructor annotations _) -> EffectConstructor annotations regions)
        (flip const)
        relationForDataTypes
        datas
        emptyEffectEnvironment
    
    envWithAnnotations = 
      writeArguments
        True
        (variableFromIndices 0)
        (\ee tp -> typeAnnotationSortArgument ee tp [])
        (\annotations _ (EffectDataType _ regions relation) -> EffectDataType annotations regions relation)
        (\annotations (EffectConstructor _ regions) -> EffectConstructor annotations regions)
        (flip const) -- TODO
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
        EffectConstructor _ regionArgs = eeLookupConstructor env name

    datas = normalizedDataTypes env mod
    initializeDataType :: Declaration DataType -> EffectEnvironment -> EffectEnvironment
    initializeDataType (Declaration name _ _ _ (DataType constructors)) effectEnv =
      effectEnv{
        -- Assign sortUnassigned to all data types, such that we can find recursion.
        eeDataTypes = insertMap name (EffectDataType sortUnassigned sortUnassigned []) $ eeDataTypes effectEnv,
        eeConstructors = foldr initializeConstructor (eeConstructors effectEnv) constructors
      }
    initializeConstructor :: Declaration DataTypeConstructorDeclaration -> IdMap EffectConstructor -> IdMap EffectConstructor
    initializeConstructor (Declaration name _ _ _ _) constructors = insertMap name (EffectConstructor [] []) constructors

sortUnassigned :: SortArgument a
sortUnassigned = SortArgumentPolymorphic (TypeVar (-1)) []

writeArguments ::
  Bool -- Should we look in function types for type dependencies
  -> (Int -> argument) -- Converts an int to an argument (as stored in the constructor)
  -> (EffectEnvironment -> Tp -> SortArgument a) -- Generates the argument sorts for types
  -> (SortArgument a -> Maybe b -> EffectDataType -> EffectDataType) -- Updates the arguments in a DataType
  -> ([Argument argument] -> EffectConstructor -> EffectConstructor) -- Updates the arguments in a Constructor
  -> (SortArgument a -> a -> a) -- Apply / instantiate a field
  -> (EffectEnvironment -> [Declaration DataType] -> b) -- Additional computations, used for computing the relation of 
  -> [Declaration DataType]
  -> EffectEnvironment
  -> EffectEnvironment -- Resulting effect environment
writeArguments inFunctions var arguments update updateCon instantiate additional declarations initialEnv = foldl handleGroup initialEnv groups
  where
    handleGroup :: EffectEnvironment -> BindingGroup DataType -> EffectEnvironment
    handleGroup e group = updateDataTypes (SortArgumentList vars) (Just additionalData) e'
      where
        e' = foldr updateConstructor e constructorArguments

        -- Temp environment, used to compute additionalData
        e'' = updateDataTypes (SortArgumentList vars) Nothing e'
        additionalData = additional e'' list
        updateDataTypes sort additionalData e = foldr (updateDataType sort additionalData) e list
        updateDataType sort additionalData (Declaration name _ _ _ _) env =
          env{ eeDataTypes = insertMapWith
            name
            (error "Region.DataType: data type not found in environment")
            (update sort additionalData)
            $ eeDataTypes env
          }
        updateConstructor (name, sort) env =
          env{ eeConstructors = insertMapWith
            name
            (error "Region.DataType: constructor not found in environment")
            (updateCon sort)
            $ eeConstructors env
          }
          where

        list :: [Declaration DataType]
        list = bindingGroupToList group
        sorts = list >>= dataTypeSort
        argumentRecursion = ArgumentList $ zipWith (\_ idx -> ArgumentValue $ var idx) vars [0..]
        (_, constructorArguments) = mapAccumL
          (\next (name, argSorts) ->
            let
              (next', args) = mapAccumL (sortToArgument var argumentRecursion) next argSorts
            in
              (next', (name, args))
          )
          0
          sorts
        vars = sorts >>= (\(_, sort) -> sort >>= sortArgumentFlatten)
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

sortArgumentFlatten :: SortArgument a -> [SortArgument a] -- Result does not contain SortArgumentList
sortArgumentFlatten (SortArgumentList args) = args >>= sortArgumentFlatten
sortArgumentFlatten (SortArgumentPolymorphic (TypeVar (-1)) []) = [] -- Type variable for recursion. Does not add additional region/annotation variables, so we can ignore this.
sortArgumentFlatten arg = [arg]

sortToArgument :: (Int -> b) -> Argument b -> Int -> SortArgument a -> (Int, Argument b)
sortToArgument var arguments next (SortArgumentList sorts)
  = (next', ArgumentList as)
  where
    (as, next') = toArguments next sorts
    toArguments n [] = ([], n)
    toArguments n (x:xs) = (y:ys, n'')
      where
        (n', y) = sortToArgument var arguments n x
        (ys, n'') = toArguments n' xs
sortToArgument var arguments next (SortArgumentPolymorphic (TypeVar (-1)) []) = (next, arguments) -- Recursion - apply with the same arguments
sortToArgument var arguments next _ = (next + 1, ArgumentValue $ var next)
