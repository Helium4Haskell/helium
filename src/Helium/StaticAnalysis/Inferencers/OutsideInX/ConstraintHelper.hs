module Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper where

import Data.Maybe
import qualified Data.Map as M

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU

import Top.Types.Classes

import Unbound.Generics.LocallyNameless

monotypeTuple :: [MonoType] -> MonoType
monotypeTuple vars = let
    tupleType = "(" ++ replicate (length vars - 1) ',' ++ ")"
    in conApply tupleType vars

monotypeList :: MonoType -> MonoType
monotypeList elem = conApply "[]" [elem] 

