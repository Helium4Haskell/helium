module Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes

monotypeTuple :: [MonoType] -> MonoType
monotypeTuple vars = let
    tupleType = "(" ++ replicate (length vars - 1) ',' ++ ")"
    in conApply tupleType vars

monotypeList :: MonoType -> MonoType
monotypeList elem' = conApply "[]" [elem'] 

