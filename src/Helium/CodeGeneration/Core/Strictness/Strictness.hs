module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import qualified Helium.CodeGeneration.Core.Strictness.MonoType as MT
import qualified Helium.CodeGeneration.Core.Strictness.MonoDataType as DT
import qualified Helium.CodeGeneration.Core.Strictness.MonovariantAdvanced as MA
import qualified Helium.CodeGeneration.Core.Strictness.MonovariantSimple as MS
import qualified Helium.CodeGeneration.Core.Strictness.PolyvariantAdvanced as PA
import qualified Helium.CodeGeneration.Core.Strictness.PolyvariantSimple as PS
import qualified Helium.CodeGeneration.Core.Strictness as Old

import Lvm.Common.Id
import Lvm.Core.Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: Int -> NameSupply -> CoreModule -> CoreModule
-- Select variant of strictness analysis
coreStrictness 7 = DT.monovariantStrictness
coreStrictness 6 = MT.monovariantStrictness
coreStrictness 5 = PS.polyvariantStrictness
coreStrictness 4 = MS.monovariantStrictness
coreStrictness 3 = PA.polyvariantStrictness
coreStrictness 2 = MA.monovariantStrictness
coreStrictness 1 = Old.coreStrictness
coreStrictness _ = \_ x -> x -- No strictness
