module Helium.CodeGeneration.Iridium.Region.Env where

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import qualified Data.IntMap.Strict as IntMap

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation


-- Environment indexed by Debruijn indices
-- The environment is represented as a map of Debruijn levels
data Env a = Env !Int (IntMap.IntMap a)

emptyEnv :: Env a
emptyEnv = Env 0 IntMap.empty

envPush :: a -> Env a -> Env a
envPush a (Env n m) = Env (n + 1) $ IntMap.insert n a m

envLookup :: Int -> Env a -> Maybe a
envLookup idx (Env n m) = case IntMap.lookup (n - idx - 1) m of
  Nothing
    | idx < 0 || idx >= n -> Nothing
    | otherwise -> error "Helium.CodeGeneration.Iridium.Region.Env.envLookup: Env has an invalid state"
  Just x -> Just x

envFind :: Int -> Env a -> a
envFind idx (Env n m) = case IntMap.lookup (n - idx - 1) m of
  Nothing
    | idx < 0 || idx >= n -> error $ "Helium.CodeGeneration.Iridium.Region.Env.envFind: Invalid Debruijn index: " ++ show idx
    | otherwise -> error "Helium.CodeGeneration.Iridium.Region.Env.envFind: Env has an invalid state"
  Just x -> x

envSize :: Env a -> Int
envSize (Env s _) = s

type DataTypeEnv = IdMap DataTypeSort
data DataTypeSort = DataTypeSort !Relation !Sort !RegionSort -- Containment relation, annotation sort, region sort

-- The type cannot contain any type synonyms; they should be expanded before performing region inference.
sortOfType :: DataTypeEnv -> Type -> Sort
sortOfType env tp = sortOfType' env tp []

sortOfType' :: DataTypeEnv -> Type -> [Type] -> Sort
sortOfType' env = sort'
  where
    sort' :: Type -> [Type] -> Sort
    sort' (TAp t1 t2)      args = sort' t1 (t2 : args)

    sort' (TForall q _ t1) []   = SortForall q $ sort' t1 []
    sort' (TForall _ _ t1) (t2:tps) = sort' (typeSubstitute 0 t2 t1) tps

    sort' (TStrict t1)     []   = sort' t1 []
    sort' (TStrict _)      _    = error "Helium.CodeGeneration.Iridium.Region.Env.sortOfType: Invalid strictness type"

    sort' (TVar var)       args = SortPolymorphic var args
    sort' (TCon TConFun)   [tArg, tReturn] =
      SortFun annotationArg regionArg LifetimeContextAny $ SortTuple
        [ SortFun SortUnit RegionSortMonomorphic LifetimeContextAny
          $ SortFun SortUnit regionReturn LifetimeContextLocalBottom SortRelation
        , annotationReturn
        ]
      where
        annotationArg = sortOfType env tArg
        regionArg = regionSortOfType env $ typeNotStrict tArg

        annotationReturn = sortOfType env tReturn
        regionReturn = regionSortOfType env (typeToStrict tReturn)
    sort' (TCon con)       args = case con of
      TConFun -> error "Helium.CodeGeneration.Iridium.Region.Env.sortOfType: Invalid function type"
      TConTuple _ -> SortTuple $ map (sortOfType env) args
      TConDataType name -> dataType name
      TConTypeClassDictionary name -> dataType $ dictionaryDataTypeName name
      where
        dataType name = case lookupMap name env of
          Nothing -> error $ "Helium.CodeGeneration.Iridium.Region.Env.sortOfType: Data type not found in environment: " ++ stringFromId name
          Just (DataTypeSort _ s _) -> s

regionSortOfType :: DataTypeEnv -> Type -> RegionSort
regionSortOfType env tp
  | typeIsStrict tp = RegionSortTuple
    [ RegionSortMonomorphic -- Region for the value
    , regionChildSortOfType env tp
    ]
  | otherwise = RegionSortTuple
    [ RegionSortMonomorphic
    , RegionSortMonomorphic
    , regionChildSortOfType env tp
    ]

regionChildSortOfType :: DataTypeEnv -> Type -> RegionSort
regionChildSortOfType env tp = regionChildSortOfType' env tp []

regionChildSortOfType' :: DataTypeEnv -> Type -> [Type] -> RegionSort
regionChildSortOfType' env = regionSort'
  where
    regionSort' (TAp t1 t2)      args = regionSort' t1 (t2 : args)

    regionSort' (TForall q _ t1) []   = RegionSortForall q $ regionSort' t1 []
    regionSort' (TForall _ _ t1) (t2:tps) = regionSort' (typeSubstitute 0 t2 t1) tps

    regionSort' (TStrict t1)     []   = regionSort' t1 []
    regionSort' (TStrict _)      _    = error "Helium.CodeGeneration.Iridium.Region.Env.regionSortOfType: Invalid strictness type"

    regionSort' (TVar var)       args = RegionSortPolymorphic var args
    regionSort' (TCon con)       args = case con of
      TConFun -> RegionSortUnit
      TConTuple _ -> RegionSortTuple $
      -- For each field, a region for the thunk, a region for the value and region variables for the fields / children of the element
        args >>= (\tp -> [RegionSortMonomorphic, RegionSortMonomorphic, regionChildSortOfType' env tp []])
      TConDataType name -> dataType name
      TConTypeClassDictionary name -> dataType $ dictionaryDataTypeName name
      where
        dataType name = case lookupMap name env of
          Nothing -> error $ "Helium.CodeGeneration.Iridium.Region.Env.regionSortOfType: Data type not found in environment: " ++ stringFromId name
          Just (DataTypeSort _ _ s) -> s

sortInstantiate :: DataTypeEnv -> Sort -> Type -> Sort
sortInstantiate env (SortForall _ s) tp = sortSubstitute env 0 tp s
sortInstantiate _ s _ = error $ "Helium.CodeGeneration.Iridium.Region.Env.sortInstantiate: Cannot instantiate this sort, expected SortForall, got " ++ showSort [] s ""

sortSubstitute :: DataTypeEnv -> Int -> Type -> Sort -> Sort
sortSubstitute env forallCount tp s = case s of
  SortForall q s1 -> SortForall q $ sortSubstitute env (forallCount + 1) tp s1
  SortFun s1 rs1 lifetime s2 -> SortFun (substitute s1) (regionSortSubstitute env forallCount tp rs1) lifetime (substitute s2)
  SortTuple sorts -> SortTuple $ substitute <$> sorts
  SortRelation -> SortRelation
  SortPolymorphic idx tps ->
    let
      tp' = typeWeaken forallCount tp
      tps' = typeSubstitute forallCount tp' <$> tps
    in
      if idx == forallCount then
        sortOfType' env tp' tps'
      else
        SortPolymorphic (if idx < forallCount then idx else idx - 1) tps'
  where
    substitute = sortSubstitute env forallCount tp

regionSortSubstitute :: DataTypeEnv -> Int -> Type -> RegionSort -> RegionSort
regionSortSubstitute env forallCount tp rs = case rs of
  RegionSortForall q s -> RegionSortForall q $ regionSortSubstitute env (forallCount + 1) tp s
  RegionSortTuple sorts -> RegionSortTuple $ regionSortSubstitute env forallCount tp <$> sorts
  RegionSortMonomorphic -> RegionSortMonomorphic
  RegionSortPolymorphic idx tps ->
    let
      tp' = typeWeaken forallCount tp
      tps' = typeSubstitute forallCount tp' <$> tps
    in
      if idx == forallCount then
        regionChildSortOfType' env tp' tps'
      else
        RegionSortPolymorphic (if idx < forallCount then idx else idx - 1) tps'

