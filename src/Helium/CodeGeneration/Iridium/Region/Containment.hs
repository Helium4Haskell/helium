{-
Generates constraints to ensure containment, meaning that objects in fields should life at least as long as their container.
For instance, in a type (Bar, Foo), Bar and Foo should outlive the tuple.
-}

module Helium.CodeGeneration.Iridium.Region.Containment (containment) where

import Data.List
import Lvm.Common.IdMap
import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Utils

-- Generates constraints to ensure containment, meaning that objects in fields should life at least as long as their container.
-- For instance, in a type (Bar, Foo), Bar and Foo should outlive the tuple.
-- Type should be normalized
containment :: EffectEnvironment -> Tp -> Argument RegionVar -> [RelationConstraint]
containment env = containment' [] Nothing
  where
    containmentConstraint :: Maybe RegionVar -> RegionVar -> [RelationConstraint]
    containmentConstraint Nothing _ = []
    containmentConstraint (Just parent) child = [child `Outlives` parent]

    containment' :: [RelationConstraint] -> Maybe RegionVar -> Tp -> Argument RegionVar -> [RelationConstraint]
    containment' accum parent tp (ArgumentList [ArgumentValue region, fields])
      | tpIsStrict tp =
        let accum' = containmentConstraint parent region ++ accum
        in containmentFields accum region (tpNotStrict tp) [] fields
    containment' accum parent tp (ArgumentList [ArgumentValue regionThunk, ArgumentValue regionValue, fields])
      | not $ tpIsStrict tp =
        let accum' = containmentConstraint parent regionThunk ++ [regionValue `Outlives` regionThunk] ++ accum
        in containmentFields accum regionValue (tpNotStrict tp) [] fields
    containment' _ _ _ _ = error "containment: invalid region annotation"

    containmentFields :: [RelationConstraint] -> RegionVar -> Tp -> [Tp] -> Argument RegionVar -> [RelationConstraint]
    containmentFields accum parent (TpVar _) _ (ArgumentValue r) = Outlives r parent : accum
    containmentFields accum parent (TpApp t1 t2) tArgs regions = containmentFields accum parent t1 (t2 : tArgs) regions
    containmentFields accum parent (TpForall tp) [] regions = containmentFields accum parent tp [] regions
    containmentFields accum parent (TpCon (TConDataType name)) tArgs (ArgumentList regions) = containmentDataType parent name tArgs regions
    containmentFields accum parent (TpCon (TConTypeClassDictionary name)) tArgs (ArgumentList regions) = containmentDataType parent (dictionaryDataTypeName name) tArgs regions
    containmentFields accum parent (TpCon (TConTuple 0)) [] (ArgumentList []) = accum
    containmentFields accum parent (TpCon (TConTuple arity)) (t1:tArgs) (ArgumentList (ArgumentValue rThunk : ArgumentValue rValue : argumentElement : argumentRest))
      = containmentFields accum2 parent (TpCon $ TConTuple $ arity - 1) tArgs (ArgumentList argumentRest)
      where
        accum1 = Outlives rValue rThunk : accum
        accum2 = containmentFields accum1 rValue t1 [] argumentElement
    containmentFields accum parent (TpCon TConFun) _  _ = accum
    containmentFields _ _ tp _ arg = error ("containment: type is not normalized or region arguments does not match. Type: " ++ show tp ++ ", region arguments: " ++ show arg)
    
    containmentDataType :: RegionVar -> Id -> [Tp] -> [Argument RegionVar] -> [RelationConstraint]
    containmentDataType parent name typeArgs regionArgs = constraintsDataType ++ constraintsFields
      where
        EffectDataType _ argSort constraints = eeLookupDataType env name
        constraintsDataType = instantiateRelationConstraints (\var -> Just $ argumentFlatten (regionArgs !!! indexInArgument var)) constraints
        constraintsFields = concat $ zipWith fieldConstraints argSort regionArgs

        -- Gather constraints per region argument of the data type. Any region argument should outlive the region variable of the object.
        -- Furthermore, polymorphic arguments may give more constraints when we instantiate them.
        fieldConstraints :: SortArgumentRegion -> Argument RegionVar -> [RelationConstraint]
        fieldConstraints (SortArgumentRegionPolymorphic (TypeVar tvar) tvarTypeArgs) arg = containmentFields [] parent tp tvarTypeArgs arg
          where
            tp = case tryIndex typeArgs (length typeArgs - tvar - 1) of
              Nothing -> error $ "containment: type variable not found. " ++ show typeArgs ++ "; " ++ show tvar
              Just tp -> tp
        fieldConstraints _ (ArgumentValue region) = [region `Outlives` parent]
        fieldConstraints s a = error $ "fieldConstraints: Illegal arguments: " ++ show s ++ "; " ++ show a
