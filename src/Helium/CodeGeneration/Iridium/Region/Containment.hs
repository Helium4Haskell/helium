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

-- Generates constraints to ensure containment, meaning that objects in fields should life at least as long as their container.
-- For instance, in a type (Bar, Foo), Bar and Foo should outlive the tuple.
-- Type should be normalized
containment :: EffectEnvironment -> Type -> Argument RegionVar -> [RelationConstraint]
containment env = containment' [] Nothing
  where
    containmentConstraint :: Maybe RegionVar -> RegionVar -> [RelationConstraint]
    containmentConstraint Nothing _ = []
    containmentConstraint (Just parent) child = [child `Outlives` parent]

    containment' :: [RelationConstraint] -> Maybe RegionVar -> Type -> Argument RegionVar -> [RelationConstraint]
    containment' accum parent tp (ArgumentList [ArgumentValue region, fields])
      | typeIsStrict tp =
        let accum' = containmentConstraint parent region ++ accum
        in containmentFields accum region (typeNotStrict tp) [] fields
    containment' accum parent tp (ArgumentList [ArgumentValue regionThunk, ArgumentValue regionValue, fields])
      | not $ typeIsStrict tp =
        let accum' = containmentConstraint parent regionThunk ++ [regionValue `Outlives` regionThunk] ++ accum
        in containmentFields accum regionValue (typeNotStrict tp) [] fields
    containment' _ _ _ _ = error "containment: invalid region annotation"

    containmentFields :: [RelationConstraint] -> RegionVar -> Type -> [Type] -> Argument RegionVar -> [RelationConstraint]
    containmentFields accum parent (TVar _) _ (ArgumentValue r) = Outlives r parent : accum
    containmentFields accum parent (TAp t1 t2) tArgs regions = containmentFields accum parent t1 (t2 : tArgs) regions
    containmentFields accum parent (TForall _ _ tp) [] regions = containmentFields accum parent tp [] regions
    containmentFields accum parent (TCon (TConDataType name)) tArgs (ArgumentList regions) = containmentDataType parent name tArgs regions
    containmentFields accum parent (TCon (TConTypeClassDictionary name)) tArgs (ArgumentList regions) = containmentDataType parent (dictionaryDataTypeName name) tArgs regions
    containmentFields accum parent (TCon (TConTuple 0)) [] (ArgumentList []) = accum
    containmentFields accum parent (TCon (TConTuple arity)) (t1:tArgs) (ArgumentList (ArgumentValue rThunk : ArgumentValue rValue : argumentElement : argumentRest))
      = containmentFields accum2 parent (TCon $ TConTuple $ arity - 1) tArgs (ArgumentList argumentRest)
      where
        accum1 = Outlives rValue rThunk : accum
        accum2 = containmentFields accum1 rValue t1 [] argumentElement
    containmentFields accum parent (TCon TConFun) _  _ = accum
    containmentFields _ _ tp _ arg = error ("containment: type is not normalized or region arguments does not match. Type: " ++ showType [] tp ++ ", region arguments: " ++ show arg)
    
    containmentDataType :: RegionVar -> Id -> [Type] -> [Argument RegionVar] -> [RelationConstraint]
    containmentDataType parent name typeArgs regionArgs = constraintsDataType ++ constraintsFields
      where
        EffectDataType typeVars _ argSort constraints = eeLookupDataType env name
        constraintsDataType = instantiateRelationConstraints (\(RegionVar idx) -> Just $ argumentFlatten (regionArgs !! idx)) constraints
        constraintsFields = case argSort of
          SortArgumentList argSorts ->
            concat $ zipWith fieldConstraints argSorts regionArgs
          s -> error ("containment: data type " ++ show name ++ " has wrong region argument sort: " ++ show s)

        typeVarInstantiation :: [(TypeVar, Type)]
        typeVarInstantiation = zip typeVars typeArgs

        -- Gather constraints per region argument of the data type. Any region argument should outlive the region variable of the object.
        -- Furthermore, polymorphic arguments may give more constraints when we instantiate them.
        fieldConstraints :: SortArgument SortArgumentRegion -> Argument RegionVar -> [RelationConstraint]
        fieldConstraints (SortArgumentPolymorphic tvar tvarTypeArgs) arg = containmentFields [] parent tp tvarTypeArgs arg
          where
            tp = case lookup tvar typeVarInstantiation of
              Nothing -> error "containment: Illegal data type, type var not found"
              Just t -> t
        fieldConstraints _ (ArgumentValue region) = [region `Outlives` parent]
