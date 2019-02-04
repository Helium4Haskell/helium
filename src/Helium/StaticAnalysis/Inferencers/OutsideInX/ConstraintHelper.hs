module Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper where

import Cobalt.Core

monotypeTuple :: [MonoType] -> MonoType
monotypeTuple vars = let
    tupleType = "(" ++ replicate (length vars - 1) ',' ++ ")"
    in MonoType_Con tupleType vars

monotypeList :: MonoType -> MonoType
monotypeList elem = MonoType_Con "[]" [elem] 