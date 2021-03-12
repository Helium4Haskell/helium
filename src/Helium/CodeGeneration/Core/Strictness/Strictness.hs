module Helium.CodeGeneration.Core.Strictness.Strictness (coreStrictness) where

import Helium.CodeGeneration.Core.Strictness.Annotate
import Helium.CodeGeneration.Core.Strictness.Analyse
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Transform

import Lvm.Common.Id
import Lvm.Core.Expr

-- Turn expressions which are guaranteed to be evaluated to strict
coreStrictness :: NameSupply -> CoreModule -> CoreModule
coreStrictness supply mod = mod''
  where
    -- Annotate types
    mod'  = annotateModule supply mod
    -- Run analysis
    cs    = analyseModule mod'
    -- Solve constraints
    cs'   = solveConstraints cs
    -- Apply transformations
    mod'' = transformModule cs' mod'
