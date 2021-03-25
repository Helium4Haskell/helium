{-| Module      :  Core
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.Core (desugarCore) where

import Lvm.Common.Id
import Lvm.Core.Expr
import Helium.CodeGeneration.Core.TypeCheck
import Control.Monad (when)
import Text.PrettyPrint.Leijen (pretty)
import Helium.CodeGeneration.Iridium.FileCache

import Helium.CodeGeneration.Core.LetInline(coreLetInline)
import Helium.CodeGeneration.Core.LetSort(coreLetSort)
import Helium.CodeGeneration.Core.Normalize(coreNormalize)
import Helium.CodeGeneration.Core.Lift(coreLift)
import Helium.CodeGeneration.Core.ReduceThunks(coreReduceThunks)
import Helium.CodeGeneration.Core.Rename(coreRename)
import Helium.CodeGeneration.Core.RemoveAliases(coreRemoveAliases)
import Helium.CodeGeneration.Core.Saturate(coreSaturate)
import Helium.CodeGeneration.Core.Strictness as S0 (coreStrictness)
import Helium.CodeGeneration.Core.Strictness.Strictness as S1 (coreStrictness)

pipeline :: Int -> [(String, NameSupply -> CoreModule -> CoreModule)]
pipeline s =
  [ ("Rename", coreRename)
  , ("Saturate", coreSaturate)
  , ("LetSort", const coreLetSort)
  , ("LetInline 1", const coreLetInline)
  , ("LetInline 2", const coreLetInline)
  , ("Normalize", coreNormalize)
  , ("Strictness 1", selectStrictness s)
  , ("Strictness 2", selectStrictness s)
  , ("RemoveAliases", const coreRemoveAliases)
  , ("ReduceThunks", const coreReduceThunks)
  , ("Lift", coreLift)
  , ("Strictness 3", selectStrictness s)
  ]

-- Desugars core. The desugared AST can be converted to Iridium.
desugarCore :: Int -> NameSupply -> CoreModule -> IO CoreModule
desugarCore s supply mod = do
  putStrLn $ showStrictness s ++ " selected..."
  desugar supply (pipeline s) mod

desugar :: NameSupply -> [(String, NameSupply -> CoreModule -> CoreModule)] -> CoreModule -> IO CoreModule
desugar supply ((passName, passFn) : passes) mod = do
  --writeFile (passName ++ "_before.core") $ show $ pretty mod
  let (supply1, supply2) = splitNameSupply supply
  let mod' = passFn supply1 mod
  --writeFile (passName ++ "_after.core") $ show $ pretty mod'
  checkModuleIO passName mod'
  desugar supply2 passes mod'
desugar _ [] mod = return mod

-- Select variant of strictness analysis
selectStrictness :: Int -> (NameSupply -> CoreModule -> CoreModule)
selectStrictness 1 = S1.coreStrictness
selectStrictness _ = S0.coreStrictness -- Default strictness

showStrictness :: Int -> String
showStrictness 1 = "New strictness analysis"
showStrictness _ = "Old strictness analysis"
