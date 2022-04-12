module Helium.StaticAnalysis.Miscellaneous.Diagnostics where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfo (maybeHead)

type Diagnostics = [Diagnostic]

data Diagnostic
  = TyVarInTypeFamily TyVar Int MonoType
  deriving Show

maybeTyVarInTypeFamily :: TyVar -> Diagnostics -> Maybe Diagnostics
maybeTyVarInTypeFamily tv ds = case [diag | diag@(TyVarInTypeFamily tv' _ _) <- ds, tv == tv'] of
  [] -> Nothing
  xs -> Just xs

addTyVarInTypeFamilyList :: [(TyVar, Int)] -> MonoType -> Diagnostics
addTyVarInTypeFamilyList []       _  = []
addTyVarInTypeFamilyList ((tv, i):tvs) mt = TyVarInTypeFamily tv i mt : addTyVarInTypeFamilyList tvs mt
