module Helium.StaticAnalysis.Miscellaneous.Diagnostics where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfo (maybeHead)

type Diagnostics = [Diagnostic]

data Diagnostic
  = TyVarInTypeFamily TyVar MonoType

maybeTyVarInTypeFamily :: TyVar -> Diagnostics -> Maybe Diagnostic
maybeTyVarInTypeFamily tv ds = maybeHead [diag | diag@(TyVarInTypeFamily tv' _) <- ds, tv == tv']

addTyVarInTypeFamilyList :: [TyVar] -> MonoType -> Diagnostics
addTyVarInTypeFamilyList []       _  = []
addTyVarInTypeFamilyList (tv:tvs) mt = TyVarInTypeFamily tv mt : addTyVarInTypeFamilyList tvs mt
