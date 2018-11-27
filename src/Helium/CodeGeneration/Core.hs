{-| Module      :  Core
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core where

import Lvm.Common.Id
import Lvm.Core.Expr

import Helium.CodeGeneration.Core.LetSort(coreLetSort)
import Helium.CodeGeneration.Core.Normalize(coreNormalize)
import Helium.CodeGeneration.Core.Lift(coreLift)
import Helium.CodeGeneration.Core.ReduceThunks(coreReduceThunks)
import Helium.CodeGeneration.Core.Rename(coreRename)
import Helium.CodeGeneration.Core.RemoveAliasses(coreRemoveAliasses)
import Helium.CodeGeneration.Core.RemoveDead(coreRemoveDead)
import Helium.CodeGeneration.Core.Saturate(coreSaturate)

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: NameSupply -> CoreModule -> CoreModule
desugarCore supply = coreLift supplyLift . coreReduceThunks . coreRemoveDead . coreRemoveAliasses . coreNormalize supplyNormalize . coreLetSort . coreSaturate supplySaturate . coreRename supplyNoShadow
  where
    supplyLift : supplyNormalize : supplyFromCore : supplyNoShadow : supplySaturate : _ = splitNameSupplies supply
