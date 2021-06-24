module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Helium.CodeGeneration.Core.Strictness.Monovariant
import Helium.CodeGeneration.Core.Strictness.Polyvariant
import qualified Helium.CodeGeneration.Core.Strictness as Old

import Lvm.Common.Id
import Lvm.Core.Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: Int -> NameSupply -> CoreModule -> CoreModule
-- Select variant of strictness analysis
coreStrictness 3 = polyvariantStrictness
coreStrictness 2 = monovariantStrictness
coreStrictness 1 = Old.coreStrictness
coreStrictness _ = \_ x -> x -- No strictness
