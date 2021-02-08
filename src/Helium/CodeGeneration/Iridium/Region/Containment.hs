module Helium.CodeGeneration.Iridium.Region.Containment (containment, containment', containment'') where

import Control.Applicative
import Data.Maybe
import Data.List

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Utils

containment :: DataTypeEnv -> Type -> Relation
containment env tp = containment' env tp (regionSortToVars 0 $ regionSortOfType env tp)

containment' :: DataTypeEnv -> Type -> RegionVars -> Relation
containment' env tp vars = relationFromConstraints $ containment'' env tp vars

containment'' :: DataTypeEnv -> Type -> RegionVars -> [RelationConstraint]
containment'' env tp vars
  | typeIsStrict tp
  , RegionVarsTuple [RegionVarsSingle regionThunk, RegionVarsSingle regionValue, regionFields] <- vars
    = Outlives regionThunk regionValue
    : map (Outlives regionValue) (flattenRegionVars regionFields) 
    ++ containmentChildren env tp [] regionFields
  | not $ typeIsStrict tp
  , RegionVarsTuple [RegionVarsSingle regionValue, regionFields] <- vars
    = map (Outlives regionValue) (flattenRegionVars regionFields)
    ++ containmentChildren env tp [] regionFields
  | otherwise = error "Helium.CodeGeneration.Iridium.Region.Containment.containment'': Region vars do not match with type"

containmentChildren :: DataTypeEnv -> Type -> [Type] -> RegionVars -> [RelationConstraint]
containmentChildren env tp' tps' regionVars = go tp' tps'
  where
    go :: Type -> [Type] -> [RelationConstraint]
    go (TAp t1 t2)      args = go t1 (t2 : args)

    go (TForall _ _ t1) []   = go t1 []
    go (TForall _ _ _ ) _    = error "Helium.CodeGeneration.Iridium.Region.Containment.containmentChildren: Type is not properly normalized"

    go (TStrict t1)     []   = go t1 []
    go (TStrict _)      _    = error "Helium.CodeGeneration.Iridium.Region.Containment.containmentChildren: Invalid strictness type"

    go (TVar _)         _    = []
    go (TCon con)       args = case con of
      TConFun -> []
      TConTuple _ -> tuple args regionVars
      TConDataType name -> dataType name args 
      TConTypeClassDictionary name -> dataType (dictionaryDataTypeName name) args

    tuple :: [Type] -> RegionVars -> [RelationConstraint]
    tuple (tp:tps) (RegionVarsTuple (RegionVarsSingle regionThunk : RegionVarsSingle regionValue : regionFields : vars))
      = Outlives regionThunk regionValue
      : map (Outlives regionValue) (flattenRegionVars regionFields)
      ++ containmentChildren env tp [] regionFields
      ++ tuple tps (RegionVarsTuple vars)
    tuple [] (RegionVarsTuple []) = []
    tuple _ _ = error "Helium.CodeGeneration.Iridium.Region.Containment.containmentChildren: Invalid region vars of tuple"

    dataType :: Id -> [Type] -> [RelationConstraint]
    dataType name args = case lookupMap name env of
      Nothing -> error $ "Helium.CodeGeneration.Iridium.Region.Containment.containmentChildren: Data type not found in environment: " ++ stringFromId name
      Just (DataTypeSort relation _ rs) ->
        let
          mapVar = mapping (regionSortToVars 0 rs) regionVars
          mapConstraint (Outlives x y) = Outlives <$> mapVar x <*> mapVar y
        in
          nested env (- length args) args rs regionVars $ relationToConstraints relation >>= mapConstraint


mapping :: RegionVars -> RegionVars -> (RegionVar -> [RegionVar])
mapping left right = f
  where
    f (RegionVar idx) = m IntMap.! idx

    m = IntMap.fromList $ go left right []

    go :: RegionVars -> RegionVars -> [(Int, [RegionVar])] -> [(Int, [RegionVar])]
    go (RegionVarsSingle (RegionVar x)) vars             accum = (x, flattenRegionVars vars) : accum
    go (RegionVarsTuple [])     (RegionVarsTuple [])     accum = accum
    go (RegionVarsTuple (x:xs)) (RegionVarsTuple (y:ys)) accum = go x y $ go (RegionVarsTuple xs) (RegionVarsTuple ys) accum
    go _ _ _ = error "Helium.CodeGeneration.Iridium.Region.Containment.mapping: mismatch in region vars"

nested :: DataTypeEnv -> Int -> [Type] -> RegionSort -> RegionVars -> [RelationConstraint] -> [RelationConstraint]
nested env forallCount tps (RegionSortPolymorphic t args) vars accum
  | forallCount < 0 = error "Helium.CodeGeneration.Iridium.Region.Containment.nested: Data type with illegal kind. Not enough type arguments were passed, or data type has an incorrect region sort"
  | otherwise
    = containmentChildren env (typeSubstitutions forallCount tps $ TVar t) args' vars ++ accum
  where
    args' = typeSubstitutions forallCount tps <$> args
nested _ _ _ RegionSortMonomorphic _ accum = accum
nested _ _ _ RegionSortUnit _ accum = accum
nested env forallCount tps (RegionSortForall _ rs) vars accum = nested env (forallCount + 1) tps rs vars accum
nested env forallCount tps (RegionSortUnit) (RegionVarsTuple []) accum = accum
nested env forallCount tps (RegionSortTuple (rs:rss)) (RegionVarsTuple (v:vs)) accum
  = nested env forallCount tps rs v $ nested env forallCount tps (RegionSortTuple rss) (RegionVarsTuple vs) accum
nested _ _ _ _ _ _ = error "Helium.CodeGeneration.Iridium.Region.Containment.nested: mismatch in region sort"
