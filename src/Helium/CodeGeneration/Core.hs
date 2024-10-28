{-| Module      :  Core
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core (desugarCore) where

import Helium.Lvm.Common.Id
import Helium.Lvm.Core.Expr
import Helium.CodeGeneration.Core.TypeCheck

import Helium.CodeGeneration.Core.LetInline(coreLetInline)
import Helium.CodeGeneration.Core.LetSort(coreLetSort)
import Helium.CodeGeneration.Core.Normalize(coreNormalize)
import Helium.CodeGeneration.Core.Lift(coreLift)
import Helium.CodeGeneration.Core.ReduceThunks(coreReduceThunks)
import Helium.CodeGeneration.Core.Rename(coreRename)
import Helium.CodeGeneration.Core.RemoveAliases(coreRemoveAliases)
import Helium.CodeGeneration.Core.Saturate(coreSaturate)
import Helium.CodeGeneration.Core.Strictness(coreStrictness)

pipeline :: [(String, NameSupply -> CoreModule -> CoreModule)]
pipeline =
  [ ("Rename", coreRename)
  , ("Saturate", coreSaturate)
  , ("LetSort", const coreLetSort)
  , ("LetInline 1", const coreLetInline)
  , ("LetInline 2", const coreLetInline)
  , ("Normalize", coreNormalize)
  , ("Strictness 1", coreStrictness)
  , ("Strictness 2", coreStrictness)
  , ("RemoveAliases", const coreRemoveAliases)
  , ("ReduceThunks", const coreReduceThunks)
  , ("Lift", coreLift)
  , ("Strictness 3", coreStrictness)
  ]

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: NameSupply -> CoreModule -> IO CoreModule
desugarCore supply mod = desugar supply pipeline mod

desugar :: NameSupply -> [(String, NameSupply -> CoreModule -> CoreModule)] -> CoreModule -> IO CoreModule
desugar supply ((passName, passFn) : passes) mod = do
  let (supply1, supply2) = splitNameSupply supply
  let mod' = passFn supply1 mod
  checkModuleIO passName mod' 
  desugar supply2 passes mod'
desugar _ [] mod = return mod
