module Helium.StaticAnalysis.Miscellaneous.Diagnostics where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes

type Diagnostics = [Diagnostic]

data Diagnostic
  = TyVarInTypeFamily TyVar MonoType