{-| Module      :  Core
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core where

import Lvm.Common.Id
import Lvm.Core.Expr

import Helium.CodeGeneration.Core.Normalize(coreNormalize)
import Helium.CodeGeneration.Core.Lift(coreLift)
import Helium.CodeGeneration.Core.NoShadow(coreRename)

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: NameSupply -> CoreModule -> CoreModule
desugarCore supply = coreLift supplyLift . coreNormalize supplyNormalize . coreRename supplyNoShadow
  where
    supplyLift : supplyNormalize : supplyFromCore : supplyNoShadow : _ = splitNameSupplies supply
